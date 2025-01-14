// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.extractor

import java.io.File

import com.digitalasset.daml.bazeltools.BazelRunfiles._
import com.digitalasset.extractor.services.{CustomMatchers, ExtractorFixtureAroundAll}
import com.digitalasset.ledger.api.testing.utils.SuiteResourceManagementAroundAll
import com.digitalasset.platform.sandbox.persistence.PostgresAroundAll
import io.circe.parser._
import org.scalatest._
import scalaz.Scalaz._
//import scalaz._

@SuppressWarnings(Array("org.wartremover.warts.Any"))
class GenMapSpec
    extends FlatSpec
    with Suite
    with PostgresAroundAll
    with SuiteResourceManagementAroundAll
    with ExtractorFixtureAroundAll
    with Inside
    with Matchers
    with CustomMatchers {

  override protected def darFile =
    // FIXME https://github.com/digital-asset/daml/issues/2256
    // Change to "daml-lf/encoder/test-1.8.dar" one 1.8 is frozen
    new File(rlocation("daml-lf/encoder/test-1.dev.dar"))

  override def scenario: Option[String] = Some("GenMapMod:createContracts")

  "Lists" should "be extracted" in {
    val contracts = getContracts
    contracts should have length 4
  }

  it should "contain the correct JSON data" in {
    val contractsJson = getContracts.map(_.create_arguments)

    val expected = List(
      """
        {
          "x" : [],
          "party" : "Bob"
        }
      """,
      """
        {
          "x" : [
                  [ { "fst" : 1, "snd" : "1.0" },                            { "Left" : 0 } ]
                ],
          "party" : "Bob"
        }
      """,
      """
        {
          "x" : [
                  [ { "fst" : 1, "snd" : "1.0" },                              { "Left" : 0 } ],
                  [ { "fst" : -2, "snd" : "-2.2222222222" },                   { "Right" : "1.1111111111" } ]
                ],
          "party" : "Bob"
        }
      """,
      """
        {
          "x" : [
                  [ { "fst" : 1, "snd" : "1.0" },                               { "Left" : 0 } ],
                  [ { "fst" : -2, "snd" : "-2.2222222222" },                    { "Right" : "1.1111111111" } ],
                  [ { "fst" : -3, "snd" : "-3333333333333333333333333333.0" },  { "Right" : "-2.2222222222" } ]
                ],
          "party" : "Bob"
        }
      """
    ).traverseU(parse)

    expected should be('right) // That should only fail if this JSON^^ is ill-formatted

    contractsJson should contain theSameElementsAs expected.right.get
  }
}
