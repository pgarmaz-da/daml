// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.http

import java.io.File
import java.nio.file.Path

import akka.stream.ThrottleMode
import com.digitalasset.http.util.ExceptionOps._
import com.digitalasset.ledger.api.refinements.ApiTypes.ApplicationId
import scalaz.std.option._
import scalaz.syntax.traverse._
import scalaz.{Show, \/}

import scala.concurrent.duration._
import scala.util.Try

private[http] final case class Config(
    ledgerHost: String,
    ledgerPort: Int,
    address: String = "0.0.0.0",
    httpPort: Int,
    applicationId: ApplicationId = ApplicationId("HTTP-JSON-API-Gateway"),
    packageReloadInterval: FiniteDuration = HttpService.DefaultPackageReloadInterval,
    maxInboundMessageSize: Int = HttpService.DefaultMaxInboundMessageSize,
    jdbcConfig: Option[JdbcConfig] = None,
    staticContentConfig: Option[StaticContentConfig] = None,
    accessTokenFile: Option[Path] = None,
    wsConfig: WebsocketConfig = Config.DefaultWsConfig
)

private[http] object Config {
  import scala.language.postfixOps
  val Empty = Config(ledgerHost = "", ledgerPort = -1, httpPort = -1)
  val DefaultWsConfig = WebsocketConfig(12 hours, 20, 1 second, 20, ThrottleMode.Shaping)
}

protected case class WebsocketConfig(
    maxDuration: FiniteDuration,
    throttleElem: Int,
    throttlePer: FiniteDuration,
    maxBurst: Int,
    mode: ThrottleMode
)

private[http] abstract class ConfigCompanion[A](name: String) {

  def create(x: Map[String, String]): Either[String, A]

  def createUnsafe(x: Map[String, String]): A = create(x).fold(
    e => sys.error(e),
    identity
  )

  def validate(x: Map[String, String]): Either[String, Unit] =
    create(x).map(_ => ())

  protected def requiredField(m: Map[String, String])(k: String): Either[String, String] =
    m.get(k).filter(_.nonEmpty).toRight(s"Invalid $name, must contain '$k' field")

  @SuppressWarnings(Array("org.wartremover.warts.Any"))
  protected def optionalBooleanField(m: Map[String, String])(
      k: String): Either[String, Option[Boolean]] =
    m.get(k).traverseU(v => parseBoolean(k)(v)).toEither

  protected def parseBoolean(k: String)(v: String): String \/ Boolean =
    \/.fromTryCatchNonFatal(v.toBoolean).leftMap(e =>
      s"$k=$v must be a boolean value: ${e.description}")

  protected def requiredDirectoryField(m: Map[String, String])(k: String): Either[String, File] =
    requiredField(m)(k).flatMap(directory)

  protected def directory(s: String): Either[String, File] =
    Try(new File(s).getAbsoluteFile).toEither.left
      .map(e => e.description)
      .flatMap { d =>
        if (d.isDirectory) Right(d)
        else Left(s"Directory does not exist: ${d.getAbsolutePath}")
      }
}

private[http] final case class JdbcConfig(
    driver: String,
    url: String,
    user: String,
    password: String,
    createSchema: Boolean = false
)

private[http] object JdbcConfig extends ConfigCompanion[JdbcConfig]("JdbcConfig") {

  implicit val showInstance: Show[JdbcConfig] = Show.shows(a =>
    s"JdbcConfig(driver=${a.driver}, url=${a.url}, user=${a.user}, createSchema=${a.createSchema})")

  lazy val help: String =
    "Contains comma-separated key-value pairs. Where:\n" +
      "\tdriver -- JDBC driver class name,\n" +
      "\turl -- JDBC connection URL,\n" +
      "\tuser -- database user name,\n" +
      "\tpassword -- database user password\n" +
      "\tcreateSchema -- boolean flag, if set to true, the process will re-create database schema and terminate immediately.\n" +
      "\tExample: " + helpString(
      "org.postgresql.Driver",
      "jdbc:postgresql://localhost:5432/test?&ssl=true",
      "postgres",
      "password",
      "false")

  lazy val usage: String = helpString(
    "<JDBC driver class name>",
    "<JDBC connection url>",
    "<user>",
    "<password>",
    "<true|false>")

  override def create(x: Map[String, String]): Either[String, JdbcConfig] =
    for {
      driver <- requiredField(x)("driver")
      url <- requiredField(x)("url")
      user <- requiredField(x)("user")
      password <- requiredField(x)("password")
      createSchema <- optionalBooleanField(x)("createSchema")
    } yield
      JdbcConfig(
        driver = driver,
        url = url,
        user = user,
        password = password,
        createSchema = createSchema.getOrElse(false)
      )

  private def helpString(
      driver: String,
      url: String,
      user: String,
      password: String,
      createSchema: String): String =
    s"""\"driver=$driver,url=$url,user=$user,password=$password,createSchema=$createSchema\""""
}

private[http] final case class StaticContentConfig(
    prefix: String,
    directory: File
)

private[http] object StaticContentConfig
    extends ConfigCompanion[StaticContentConfig]("StaticContentConfig") {

  implicit val showInstance: Show[StaticContentConfig] =
    Show.shows(a => s"StaticContentConfig(prefix=${a.prefix}, directory=${a.directory})")

  lazy val help: String =
    "Contains comma-separated key-value pairs. Where:\n" +
      "\tprefix -- URL prefix,\n" +
      "\tdirectory -- local directory that will be mapped to the URL prefix.\n" +
      "\tExample: " + helpString("static", "./static-content")

  lazy val usage: String = helpString("<URL prefix>", "<directory>")

  override def create(x: Map[String, String]): Either[String, StaticContentConfig] =
    for {
      prefix <- requiredField(x)("prefix").flatMap(prefixCantStartWithSlash)
      directory <- requiredDirectoryField(x)("directory")
    } yield StaticContentConfig(prefix, directory)

  private def prefixCantStartWithSlash(s: String): Either[String, String] =
    if (s.startsWith("/")) Left(s"prefix cannot start with slash: $s")
    else Right(s)

  private def helpString(prefix: String, directory: String): String =
    s"""\"prefix=$prefix,directory=$directory\""""
}
