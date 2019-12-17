// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.resources

import java.util.Timer
import java.util.concurrent.ExecutorService

import akka.actor.ActorSystem
import akka.stream.ActorMaterializer

import scala.concurrent.{ExecutionContext, Future}

@FunctionalInterface
trait ResourceOwner[T] {
  def acquire()(implicit executionContext: ExecutionContext): Resource[T]
}

object ResourceOwner {
  def pure[T](value: T): ResourceOwner[T] =
    new FutureResourceOwner(() => Future.successful(value))

  def failed[T](exception: Throwable): ResourceOwner[T] =
    new FutureResourceOwner(() => Future.failed(exception))

  def forFuture[T](acquire: () => Future[T]): ResourceOwner[T] =
    new FutureResourceOwner(acquire)

  def forCloseable[T <: AutoCloseable](acquire: () => T): ResourceOwner[T] =
    new CloseableResourceOwner(acquire)

  def forFutureCloseable[T <: AutoCloseable](acquire: () => Future[T]): ResourceOwner[T] =
    new FutureCloseableResourceOwner(acquire)

  def forExecutorService[T <: ExecutorService](acquire: () => T): ResourceOwner[T] =
    new ExecutorServiceResourceOwner[T](acquire)

  def forTimer(acquire: () => Timer): ResourceOwner[Timer] =
    new TimerResourceOwner(acquire)

  def forActorSystem(acquire: () => ActorSystem): ResourceOwner[ActorSystem] =
    new ActorSystemResourceOwner(acquire)

  def forMaterializer(acquire: () => ActorMaterializer): ResourceOwner[ActorMaterializer] =
    new ActorMaterializerResourceOwner(acquire)
}
