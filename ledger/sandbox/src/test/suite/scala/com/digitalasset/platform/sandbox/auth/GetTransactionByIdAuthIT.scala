// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.sandbox.auth

import java.util.UUID

import com.digitalasset.ledger.api.v1.transaction_service.{
  GetTransactionByIdRequest,
  TransactionServiceGrpc
}
import io.grpc.Status
import org.scalatest.Assertion

import scala.concurrent.Future

final class GetTransactionByIdAuthIT extends ReadOnlyServiceCallAuthTests {

  override def serviceCallName: String = "TransactionService#GetTransactionById"

  override def successfulBehavior: Future[Any] => Future[Assertion] =
    expectFailure(_: Future[Any], Status.Code.NOT_FOUND)

  private lazy val request =
    new GetTransactionByIdRequest(unwrappedLedgerId, UUID.randomUUID.toString, List(mainActor))

  override def serviceCallWithToken(token: Option[String]): Future[Any] =
    stub(TransactionServiceGrpc.stub(channel), token).getTransactionById(request)

}
