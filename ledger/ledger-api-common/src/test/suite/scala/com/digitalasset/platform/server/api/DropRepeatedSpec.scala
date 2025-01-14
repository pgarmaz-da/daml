// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.server.api

import akka.actor.ActorSystem
import akka.pattern.pipe
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Sink, Source}
import akka.testkit.{TestKit, TestProbe}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.collection.immutable
import scala.concurrent.ExecutionContext

final class DropRepeatedSpec
    extends TestKit(ActorSystem(classOf[DropRepeatedSpec].getSimpleName))
    with WordSpecLike
    with Matchers
    with BeforeAndAfterAll {

  private[this] implicit val materializer: ActorMaterializer = ActorMaterializer()
  private[this] implicit val executionContext: ExecutionContext = materializer.executionContext

  override def afterAll: Unit = {
    TestKit.shutdownActorSystem(system)
  }

  "DropRepeated" should {
    "drop repeated elements" in {
      val probe = TestProbe()
      val input = immutable.Seq(1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5)

      val _ = Source(input)
        .via(DropRepeated())
        .runWith(Sink.seq)
        .pipeTo(probe.ref)
        .failed
        .foreach(fail(_))

      probe.expectMsg(Vector(1, 2, 3, 4, 5))
    }

    "does not drop duplicate elements that are not repeated" in {
      val probe = TestProbe()
      val input = immutable.Seq(1, 1, 2, 2, 1, 1, 2, 2)

      val _ = Source(input)
        .via(DropRepeated())
        .runWith(Sink.seq)
        .pipeTo(probe.ref)
        .failed
        .foreach(fail(_))

      probe.expectMsg(Vector(1, 2, 1, 2))
    }
  }
}
