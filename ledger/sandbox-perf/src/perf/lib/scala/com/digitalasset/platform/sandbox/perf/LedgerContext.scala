// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.sandbox.perf

import akka.actor.ActorSystem
import akka.pattern
import akka.stream.ActorMaterializer
import com.digitalasset.daml.lf.data.Ref.PackageId
import com.digitalasset.grpc.adapter.ExecutionSequencerFactory
import com.digitalasset.ledger.api.domain
import com.digitalasset.ledger.api.v1.active_contracts_service.ActiveContractsServiceGrpc
import com.digitalasset.ledger.api.v1.active_contracts_service.ActiveContractsServiceGrpc.ActiveContractsServiceStub
import com.digitalasset.ledger.api.v1.command_service.CommandServiceGrpc
import com.digitalasset.ledger.api.v1.command_service.CommandServiceGrpc.CommandService
import com.digitalasset.ledger.api.v1.ledger_identity_service.LedgerIdentityServiceGrpc.LedgerIdentityServiceStub
import com.digitalasset.ledger.api.v1.ledger_identity_service.{
  GetLedgerIdentityRequest,
  LedgerIdentityServiceGrpc
}
import com.digitalasset.ledger.api.v1.testing.reset_service.ResetServiceGrpc.ResetService
import com.digitalasset.ledger.api.v1.testing.reset_service.{ResetRequest, ResetServiceGrpc}
import io.grpc.{Channel, StatusRuntimeException}
import org.slf4j.LoggerFactory
import scalaz.syntax.tag._

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

final class LedgerContext(channel: Channel, packageIds: Iterable[PackageId])(
    implicit protected val mat: ActorMaterializer,
    implicit protected val esf: ExecutionSequencerFactory) {

  private val logger = LoggerFactory.getLogger(this.getClass)

  val ledgerId: domain.LedgerId =
    domain.LedgerId(
      LedgerIdentityServiceGrpc
        .blockingStub(channel)
        .getLedgerIdentity(GetLedgerIdentityRequest())
        .ledgerId)

  def reset()(implicit system: ActorSystem): Future[LedgerContext] = {
    implicit val ec: ExecutionContext = mat.executionContext
    def waitForNewLedger(retries: Int): Future[domain.LedgerId] =
      if (retries <= 0)
        Future.failed(new RuntimeException("waitForNewLedger: out of retries"))
      else {
        ledgerIdentityService
          .getLedgerIdentity(GetLedgerIdentityRequest())
          .flatMap { resp =>
            // TODO: compare with current Ledger ID and retry when not changed
            Future.successful(domain.LedgerId(resp.ledgerId))
          }
          .recoverWith {
            case _: StatusRuntimeException =>
              logger.debug(
                "waitForNewLedger: retrying identity request in 1 second. {} retries remain",
                retries - 1)
              pattern.after(1.seconds, system.scheduler)(waitForNewLedger(retries - 1))
            case t: Throwable =>
              logger.warn("waitForNewLedger: failed to reconnect!")
              throw t
          }
      }
    for {
      _ <- resetService.reset(ResetRequest(ledgerId.unwrap))
      _ <- waitForNewLedger(10)
    } yield new LedgerContext(channel, packageIds)
  }

  def ledgerIdentityService: LedgerIdentityServiceStub =
    LedgerIdentityServiceGrpc.stub(channel)

  def commandService: CommandService =
    CommandServiceGrpc.stub(channel)

  def acsService: ActiveContractsServiceStub =
    ActiveContractsServiceGrpc.stub(channel)

  def resetService: ResetService =
    ResetServiceGrpc.stub(channel)

}
