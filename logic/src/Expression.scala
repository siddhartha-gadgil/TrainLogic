package logic
import logic.Term.Const
import logic.Term.Recursive
import logic.Term.Var
import logic.Formula.Equality
import logic.Formula.And
import logic.Formula.Implies
import logic.Formula.Equivalent
import logic.Formula.Not
import logic.Formula.ForAll
import logic.Formula.Atomic
import logic.Formula.Exists
import logic.Formula.Or
import Formula._

case class Function(name: String, degree: Int) {
  def apply(args: Term*) = Term.Recursive(this, args.toVector)
}

case class Relation(name: String, degree: Int)

sealed trait Expression

sealed trait Term extends Expression {
  def =:=(that: Term) = Formula.Equality(this, that)
}

sealed trait Formula extends Expression

object Term {
  case class Var(name: String) extends Term

  case class Const(name: String) extends Term

  case class Recursive(function: Function, arguments: Vector[Term])
      extends Term {
    require(function.degree == arguments.length)
  }

  def variables(t: Term): Set[Var] = t match {
    case Const(name) => Set()
    case Recursive(function, arguments) =>
      for {
        arg: Term <- arguments.toSet
        x <- variables(arg)
      } yield x
    case Var(name) => Set(Var(name))
  }

  def showTerm(t: Term): String = t match {
    case Const(_)  => s"\u2205"
    case Var(name) => name
    case t         => t.toString
  }
}

object Formula {
  case class Equality(lhs: Term, rhs: Term) extends Formula

  case class Atomic(relation: Relation, arguments: Vector[Term])
      extends Formula {
    require(relation.degree == arguments.length)
  }

  case class Or(p: Formula, q: Formula) extends Formula

  case class And(p: Formula, q: Formula) extends Formula

  case class Implies(p: Formula, q: Formula) extends Formula

  case class Equivalent(p: Formula, q: Formula) extends Formula

  case class Not(p: Formula) extends Formula

  case class ForAll(x: Term.Var, p: Formula) extends Formula

  case class Exists(x: Term.Var, p: Formula) extends Formula

  import Term._

  def freeVariables(fmla: Formula): Set[Var] = fmla match {
    case Equality(lhs, rhs) => variables(lhs) union variables(rhs)
    case And(p, q)          => freeVariables(p) union freeVariables(q)
    case Implies(p, q)      => freeVariables(p) union freeVariables(q)
    case Equivalent(p, q)   => freeVariables(p) union freeVariables(q)
    case Not(p)             => freeVariables(p)
    case ForAll(x, p)       => freeVariables(p) - x
    case Atomic(relation, arguments) =>
      for {
        arg: Term <- arguments.toSet
        x <- variables(arg)
      } yield x
    case Exists(x, p) => freeVariables(p) - x
    case Or(p, q)     => freeVariables(p) union freeVariables(q)
  }

  def pretty(formula: Formula): String = formula match {
    case And(p, q)          => s"(${pretty(p)} \u2227 ${pretty(q)})"
    case Implies(p, q)      => s"(${pretty(p)}) \u21d2 (${pretty(q)})"
    case Not(p)             => s"(\u00ac(${pretty(p)}))"
    case Equivalent(p, q)   => s"(${pretty(p)} \u21d4 ${pretty(q)})"
    case Equality(lhs, rhs) => s"(${showTerm(lhs)} = ${showTerm(rhs)})"
    case ForAll(x, p)       => s"(\u2200${showTerm(x)}(${pretty(p)}))"
    case Exists(x, p)       => s"(\u2203${showTerm(x)}(${pretty(p)}))"
    case Atomic(relation, arguments) =>
      s"(${showTerm(arguments(0))} \u2208 ${showTerm(arguments(1))})"
    case Or(p, q) => s"(${pretty(p)} \u2228 ${pretty(q)})"
  }

}

case class Structure[A](
    domain: Set[A],
    functions: Map[Function, Vector[A] => A],
    relations: Map[Relation, Vector[A] => Boolean],
    constants: Map[Const, A]
) {
  def element(t: Term, assignments: Map[Var, A]): A =
    t match {
      case c @ Const(name) => constants(c)
      case Recursive(function, arguments) =>
        functions(function)(arguments.map(x => element(x, assignments)))
      case v @ Var(name) => assignments(v)
    }
  def isTrue(f: Formula, assignments: Map[Var, A]) : Boolean =
    f match {
      case And(p, q)                   => isTrue(p, assignments) && isTrue(q, assignments)
      case Implies(p, q)               => !isTrue(p, assignments) || isTrue(q, assignments)
      case Not(p)                      => !isTrue(p, assignments)
      case Equivalent(p, q)            => isTrue(p, assignments) == isTrue(q, assignments)
      case Equality(lhs, rhs)          => element(lhs, assignments) == element(rhs, assignments)
      case ForAll(x, p)                => 
        domain.forall(y =>
            isTrue(f, assignments + (x -> y)))
      case Exists(x, p)                => 
        domain.exists(y =>
            isTrue(f, assignments + (x -> y)))
      case Atomic(relation, arguments) => 
        relations(relation)(arguments.map(x => element(x, assignments)))
      case Or(p, q)                    => isTrue(p, assignments) || isTrue(q, assignments)
    }

    def isModel(axioms: Set[Formula]) = {
        axioms.foreach(f => require(freeVariables(f).isEmpty, s"$f has free variables ${freeVariables(f)}"))
        axioms.forall(f => isTrue(f, Map()))
    }
}

case class Model[A](axioms: Set[Formula], struct: Structure[A]){
    axioms.foreach(f => require(freeVariables(f).isEmpty, s"$f has free variables ${freeVariables(f)}"))
    axioms.foreach(f => require(struct.isTrue(f, Map()), s"formula $f does not hold for the interpretation"))
}
