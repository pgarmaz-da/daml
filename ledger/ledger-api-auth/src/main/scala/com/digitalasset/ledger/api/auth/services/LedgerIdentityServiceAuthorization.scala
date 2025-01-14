// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.ledger.api.auth.services

import com.digitalasset.grpc.adapter.utils.DirectExecutionContext
import com.digitalasset.ledger.api.auth.Authorizer
import com.digitalasset.ledger.api.v1.ledger_identity_service.{
  GetLedgerIdentityRequest,
  GetLedgerIdentityResponse,
  LedgerIdentityServiceGrpc
}
import com.digitalasset.platform.api.grpc.GrpcApiService
import com.digitalasset.platform.server.api.ProxyCloseable
import io.grpc.ServerServiceDefinition

import scala.concurrent.Future

final class LedgerIdentityServiceAuthorization(
    protected val service: LedgerIdentityServiceGrpc.LedgerIdentityService with AutoCloseable,
    private val authorizer: Authorizer)
    extends LedgerIdentityServiceGrpc.LedgerIdentityService
    with ProxyCloseable
    with GrpcApiService {

  override def getLedgerIdentity(
      request: GetLedgerIdentityRequest): Future[GetLedgerIdentityResponse] =
    authorizer.requirePublicClaims(service.getLedgerIdentity)(request)

  override def bindService(): ServerServiceDefinition =
    LedgerIdentityServiceGrpc.bindService(this, DirectExecutionContext)

  override def close(): Unit = service.close()
}
