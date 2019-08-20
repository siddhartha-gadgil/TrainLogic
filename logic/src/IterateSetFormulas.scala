package logic 
import Term._, Formula._

object IterateSetFormulas{
    def terms(numVars: Int) : Iterator[Term] =
        ((0 until(numVars)).toSet.map{n : Int => Var(s"x$n") : Term} + Const("empty-set")).toIterator
    
    val belongs = Relation("belongs", 2)

    def formulaIterator(depth: Int, numFreeVars: Int) : Iterator[Formula] = {
        val termIterator = terms(numFreeVars)
        val baseFormulas : Iterator[Formula] =
            for {
                t1 <- terms(numFreeVars)
                t2 <- terms(numFreeVars)
                fmla <- Iterator(Equality(t1, t2), Atomic(belongs, Vector(t1, t2)))
            } yield fmla
        val recFormulas : Iterator[Formula] =
            if (depth < 1) Iterator()
            else
            {
                val lower = formulaIterator(depth - 1, numFreeVars)
            for {
                fmla1 <- formulaIterator(depth - 1, numFreeVars)
                fmla2 <- formulaIterator(depth - 1, numFreeVars)
                rec <- Iterator(
                    Equivalent(fmla1, fmla2),
                    And(fmla1, fmla2),
                    Or(fmla1, fmla2),
                    Implies(fmla1, fmla2),
                    Not(fmla1)
                    )
            } yield rec
        }
        val quantifiedFormulas : Iterator[Formula] = 
            if (depth <1) Iterator() 
            else{
                val lower = formulaIterator(depth - 1, numFreeVars + 1)
                val variable = Var(s"x${numFreeVars}")
                for {
                    fmla <- lower
                    quantified <- Iterator(ForAll(variable, fmla), Exists(variable, fmla))
                } yield quantified
        }    

        baseFormulas ++ quantifiedFormulas  ++ recFormulas
    }

    def closedFormulas(depth: Int) = formulaIterator(depth, 0)

    val stream : Stream[Formula] = Stream.from(0).flatMap(closedFormulas)

    val iterator = Stream.from(0).toIterator.flatMap(closedFormulas(_))

    def showTerm(t: Term) : String = t match {
        case Const(_) => s"\u2205"
        case Var(name) => name
        case t => t.toString 
    }

    def pretty(formula: Formula): String = formula match {
        case And(p, q) => s"(${pretty(p)} \u2227 ${pretty(q)})"
        case Implies(p, q) => s"(${pretty(p)}) \u21d2 (${pretty(q)})"
        case Not(p) => s"(\u00ac(${pretty(p)}))"
        case Equivalent(p, q) => s"(${pretty(p)} \u21d4 ${pretty(q)})"
        case Equality(lhs, rhs) => s"(${showTerm(lhs)} = ${showTerm(rhs)})"
        case ForAll(x, p) => s"(\u2200${showTerm(x)}(${pretty(p)}))"
        case Exists(x, p) => s"(\u2203${showTerm(x)}(${pretty(p)}))"
        case Atomic(relation, arguments) => s"(${showTerm(arguments(0))} \u2208 ${showTerm(arguments(1))})"
        case Or(p, q) => s"(${pretty(p)} \u2228 ${pretty(q)})"
    }
}