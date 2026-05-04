def main(): Unit \ IO =
    Sys.Env.runWithIO(() ->
        Fs.FileRead.runWithIO(() ->
            runMain()
        )
    )

def runMain(): Unit \ Sys.Env + Fs.FileRead + IO = match Sys.Env.getArgs() {
    case path :: Nil =>
        match Fs.FileRead.read(path) {
            case Ok(src) => match Fresh.withFresh(() -> Parser.parseAndTypeCheck(src)) {
                case Ok(checks) => printChecks(checks)
                case Err(msg) => println("Parse error: ${msg}")
            }
            case Err(err) => println("Read error: ${err}")
        }
    case _ => println("Usage: flix run -- <source-file>")
}

def printChecks(checks: List[Check]): Unit \ IO =
    foreach ((id, cs) <- checks)
        println("${id}: ${cs}")
