// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.resources

import java.util.concurrent.atomic.AtomicBoolean

import scala.collection.generic.CanBuildFrom
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

trait Resource[A] {
  self =>

  val asFuture: Future[A]

  def release(): Future[Unit]

  def map[B](f: A => B)(implicit executionContext: ExecutionContext): Resource[B] =
    Resource(asFuture.map(f), _ => Future.successful(()), release _)

  def flatMap[B](f: A => Resource[B])(implicit executionContext: ExecutionContext): Resource[B] = {
    val nextFuture: Future[Resource[B]] =
      asFuture
        .map(f)
        // if `next.asFuture` fails, `nextFuture` should also fail
        .flatMap(next => next.asFuture.map(_ => next))
    val nextRelease = (_: B) =>
      nextFuture.transformWith {
        case Success(b) => b.release()
        case Failure(_) => Future.successful(())
    }
    Resource(nextFuture.flatMap(_.asFuture), nextRelease, release _)
  }

  def withFilter(p: A => Boolean)(implicit executionContext: ExecutionContext): Resource[A] = {
    val future = asFuture.flatMap(
      value =>
        if (p(value))
          Future.successful(value)
        else
          Future.failed(new ResourceAcquisitionFilterException()))
    Resource(future, _ => Future.successful(()), release _)
  }
}

object Resource {
  import scala.language.higherKinds

  def apply[T](
      future: Future[T],
      releaseResource: T => Future[Unit],
      releaseSubResources: () => Future[Unit] = () => Future.successful(()),
  )(implicit executionContext: ExecutionContext): Resource[T] = new Resource[T] {
    private val released: AtomicBoolean = new AtomicBoolean(false)

    final lazy val asFuture: Future[T] = future.transformWith {
      case Success(value) => Future.successful(value)
      case Failure(throwable) => release().flatMap(_ => Future.failed(throwable))
    }

    def release(): Future[Unit] =
      if (released.compareAndSet(false, true))
        future.transformWith {
          case Success(value) => releaseResource(value).flatMap(_ => releaseSubResources())
          case Failure(_) => releaseSubResources()
        } else
        Future.successful(())
  }

  def pure[T](value: T)(implicit executionContext: ExecutionContext): Resource[T] =
    Resource(Future.successful(value), _ => Future.successful(()))

  def failed[T](exception: Throwable)(implicit executionContext: ExecutionContext): Resource[T] =
    Resource(Future.failed(exception), _ => Future.successful(()))

  def sequence[T, C[X] <: TraversableOnce[X]](seq: C[Resource[T]])(
      implicit bf: CanBuildFrom[C[Resource[T]], T, C[T]],
      executionContext: ExecutionContext,
  ): Resource[C[T]] =
    seq
      .foldLeft(Resource.pure(bf()))((builderResource, elementResource) =>
        for {
          builder <- builderResource
          element <- elementResource
        } yield builder += element)
      .map(_.result())

  def sequence_[T, C[X] <: TraversableOnce[X]](seq: C[Resource[T]])(
      implicit executionContext: ExecutionContext,
  ): Resource[Unit] =
    seq
      .foldLeft(Resource.pure(()))((builderResource, elementResource) =>
        for {
          _ <- builderResource
          _ <- elementResource
        } yield ())
}
