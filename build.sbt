name := "OpticTypeclass"

organization := "org.hablapps"

inThisBuild(Seq(
  scalaOrganization := "org.typelevel",
  scalaVersion := "2.12.4-bin-typelevel-4"))

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")

scalacOptions ++= Seq(
  "-Xlint",
  "-unchecked",
  "-deprecation",
  "-feature",
  "-Ypartial-unification",
  "-language:postfixOps",
  "-language:implicitConversions",
  "-language:higherKinds")

val monocleVersion = "1.5.0"

libraryDependencies ++= Seq(
  "com.github.julien-truffaut" %%  "monocle-state"  % monocleVersion,
  "com.github.julien-truffaut" %%  "monocle-core"  % monocleVersion,
  "com.github.julien-truffaut" %%  "monocle-macro" % monocleVersion,
  "com.github.julien-truffaut" %%  "monocle-law"   % monocleVersion % "test",
  "org.scalaz" %% "scalaz-core" % "7.2.8",
  "org.scalactic" %% "scalactic" % "3.0.5", 
  "org.scalatest" %% "scalatest" % "3.0.5" % "test",
  "com.chuusai" %% "shapeless" % "2.3.3")

