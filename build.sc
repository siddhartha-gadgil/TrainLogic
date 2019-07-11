import mill._, scalalib._

object logic extends ScalaModule {
  def scalaVersion = "2.12.8"

  def bin() : define.Command[PathRef] = T.command {
    def ass = jar()
    def name: String = artifactName()
    os.makeDir.all(os.pwd / "bin")
    os.makeDir.all(os.pwd / "notes" / "bin")
    os.copy.over(ass.path, os.pwd/ "bin" / "logic.jar")
    os.copy.over(ass.path, os.pwd/ "notes" / "bin" / "logic.jar")
    ass
  }
}