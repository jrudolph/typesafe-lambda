package lambda

object Simple {

  sealed trait Exp[T]
  case class C(i: Int) extends Exp[Int]
  case class Lam[T](body: Exp[T]) extends Exp[() ⇒ T]

  case class Add(e1: Exp[Int], e2: Exp[Int]) extends Exp[Int]
  case class Apply[T](e1: Exp[() ⇒ T]) extends Exp[T]

  object Interp {
    def eval[T](e: Exp[T]): T =
      e match {
        case C(i) ⇒ i
        case Lam(body) ⇒ () ⇒ eval(body)

        case Add(e1, e2) ⇒ eval(e1) + eval(e2)
        case Apply(e1) ⇒ eval(e1).apply()
      }
  }
}

object TestSimple extends App {
  import Simple._

  println(Interp.eval(Add(C(1), C(2))))

  // doesn't compile
  // println(Interp.eval(Add(C(1), Lam(C(2)))))

  println(Interp.eval(Add(C(40), Apply(Lam(C(2))))))
}