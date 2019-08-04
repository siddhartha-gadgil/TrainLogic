package logic

case class Function(name: String, degree: Int){
    def apply(args: Term*) = Term.Recursive(this, args.toVector)
}

case class Relation(name: String, degree: Int)

sealed trait Expression

sealed trait Term extends Expression{
    def =:=(that: Term) = Formula.Equality(this, that)
}

sealed trait Formula extends Expression

object Term{
    case class Var(name: String) extends Term
    
    case class Const(name: String) extends Term 

    case class Recursive(function: Function, arguments: Vector[Term]) extends Term{
        require(function.degree == arguments.length)
    }
}

object Formula{
    case class Equality(lhs: Term, rhs: Term) extends Formula
    
    case class Atomic(relation: Relation, arguments: Vector[Term]) extends Formula{
        require(relation.degree == arguments.length)
    }

    case class Or(p: Formula, q: Formula) extends Formula

    case class And(p: Formula, q: Formula) extends Formula

    case class Implies(p: Formula, q: Formula) extends Formula

    case class Equivalent(p: Formula, q: Formula) extends Formula

    case class Not(p: Formula) extends Formula

    case class ForAll(x: Term.Var, p: Formula) extends Formula

    case class Exists(x: Term.Var, p: Formula) extends Formula

}