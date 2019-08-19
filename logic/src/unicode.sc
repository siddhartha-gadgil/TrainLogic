import pprint.Tree
repl.pprinter.bind(pprint.PPrinter.Color.copy(additionalHandlers = {case s: String => Tree.Literal(s)})) 