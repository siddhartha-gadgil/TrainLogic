package logic 
import Term._, Formula._

object SetFormulas{
    def terms(numVars: Int) : Set[Term] =
        (0 until(numVars)).toSet.map{n : Int => Var(s"x$n") : Term} + Const("empty-set")
    
    val belongs = Relation("belongs", 2)

    def formulaSet(depth: Int, numFreeVars: Int) : Set[Formula] = {
        val termSet = terms(numFreeVars)
        val baseFormulas : Set[Formula] =
            for {
                t1 <- termSet
                t2 <- termSet
                fmla <- Set(Equality(t1, t2), Atomic(belongs, Vector(t1, t2)))
            } yield fmla
        val recFormulas : Set[Formula] =
            if (depth < 1) Set()
            else
            {
                val lower = formulaSet(depth - 1, numFreeVars)
            for {
                fmla1 <- lower
                fmla2 <- lower
                rec <- Set(
                    Equivalent(fmla1, fmla2),
                    And(fmla1, fmla2),
                    Or(fmla1, fmla2),
                    Implies(fmla1, fmla2),
                    Not(fmla1)
                    )
            } yield rec
        }
        val quantifiedFormulas : Set[Formula] = 
            if (depth <1) Set() 
            else{
                val lower = formulaSet(depth - 1, numFreeVars + 1)
                val variable = Var(s"x${numFreeVars}")
                for {
                    fmla <- lower
                    quantified <- Set(ForAll(variable, fmla), Exists(variable, fmla))
                } yield quantified
        }    

        baseFormulas union recFormulas union quantifiedFormulas
    }

    def closedFormulas(depth: Int) = formulaSet(depth, 0)

    val stream : Stream[Formula] = Stream.from(0).flatMap(closedFormulas)

    val iterator = stream.toIterator

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