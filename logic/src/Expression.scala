package logic
import logic.Term.Const
import logic.Term.Recursive
import logic.Term.Var
import logic.Formula.Atomic
import logic.Formula.Implies
import logic.Formula.ForAll
import logic.Formula.Exists
import logic.Formula.Or
import logic.Formula.Equivalent
import logic.Formula.And
import logic.Formula.Not
import logic.Formula.Equality

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

    def variables(t: Term) : Set[Var] = t match {
        case Const(name) => Set()
        case Recursive(function, arguments) => arguments.map(variables).reduce(_ union _)
        case Var(name) => Set(Var(name))
    }
}

object Formula{
    case class Equality(lhs: Term, rhs: Term) extends Formula
    
    case class Atomic(relation: Relation, arguments: Vector[Term]) extends Formula{
        require(relation.degree == arguments.length)
    }

    case class Or(P: Formula, Q: Formula) extends Formula

    case class And(P: Formula, Q: Formula) extends Formula

    case class Implies(P: Formula, Q: Formula) extends Formula

    case class Equivalent(P: Formula, Q: Formula) extends Formula

    case class Not(P: Formula) extends Formula

    case class ForAll(x: Term.Var, P: Formula) extends Formula

    case class Exists(x: Term.Var, P: Formula) extends Formula

    def freeVariables(fmla: Formula) : Set[Var] = fmla match {
        case Atomic(relation, arguments) => arguments.flatMap(term.variables).reduce(_ union _)
        case Implies(p, q) => freeVariables(p) union freeVariables(q)
        case ForAll(x, p) => freeVariables(p) - x
        case Exists(x, p) => freeVariables(p) - x
        case Or(p, q) => freeVariables(p) union freeVariables(q)
        case Equivalent(p, q) => freeVariables(p) union freeVariables(q)
        case And(p, q) => freeVariables(p) union freeVariables(q)
        case Not(p) => freeVariables(p) 
        case Equality(lhs, rhs) =>freeVariables(p) union freeVariables(q)
    }

}