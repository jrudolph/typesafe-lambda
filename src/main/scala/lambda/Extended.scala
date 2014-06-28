package lambda

import scala.language.reflectiveCalls

object Extended {
  // Basics

  // type level numerals
  sealed trait Nat
  case object _0 extends Nat
  case class Succ[I <: Nat](i: I) extends Nat

  type _0 = _0.type
  type _1 = Succ[_0]
  type _2 = Succ[_1]
  type _3 = Succ[_2]
  type _4 = Succ[_3]
  type _5 = Succ[_4]

  // type level maybe
  sealed trait MaybeT
  case class SomeT[T](t: T) extends MaybeT
  case object NoneT extends MaybeT
  type NoneT = NoneT.type

  // hlist of maybe's
  sealed trait HList
  case class ::[T <: MaybeT, L <: HList](head: T, tail: L) extends HList
  case object HNil extends HList
  type HNil = HNil.type

  // Auxilliary type-level functions

  // Accessor that extracts the Nth element of type T from an HList, `Res` denotes the
  // expected "shape" of an HList from which to extract something.
  //
  // Examples:
  //   At[_0, Int].Res = SomeT[Int] :: HNil
  //   At[_2, Int].Res = NoneT :: NoneT :: SomeT[Int] :: HNil
  // etc.
  trait At[N <: Nat, T] {
    type Res <: HList
    def apply(env: Res): T
  }
  implicit def atZero[T] =
    new At[_0, T] {
      type Res = SomeT[T] :: HNil
      def apply(env: Res): T = env.head.t
    }
  implicit def at[P <: Nat, T](implicit at: At[P, T]) =
    new At[Succ[P], T] {
      type Res = NoneT :: at.Res
      def apply(env: Res): T = at(env.tail)
    }

  // Evidence that two HLists of expected environments can be merged
  //
  // rules for merging:
  //
  // For head elements:
  //
  // 1. (NoneT, NoneT) = NoneT
  // 2a. (SomeT[T], NoneT) = SomeT[T]
  // 2b. (NoneT, SomeT[T]) = SomeT[T]
  // 3. forall t (SomeT[t], SomeT[t]) = SomeT[t]
  // 4. (SomeT[A], SomeT[B]) = fail
  //
  // For complete lists:
  //
  // 5a. (x, HNil) = x
  // 5b. (HNil, x) = x
  trait Merge[A <: HList, B <: HList] {
    type Res <: HList

    def aEnv(res: Res): A
    def bEnv(res: Res): B
  }
  implicit def mergeHNil = new Merge[HNil, HNil] {
    type Res = HNil

    def aEnv(res: Res) = HNil
    def bEnv(res: Res) = HNil
  }
  implicit def mergeTopNone[T1 <: HList, T2 <: HList](implicit inner: Merge[T1, T2]) =
    new Merge[NoneT :: T1, NoneT :: T2] {
      type Res = NoneT :: inner.Res

      def aEnv(res: Res) = ::(NoneT, inner.aEnv(res.tail))
      def bEnv(res: Res) = ::(NoneT, inner.bEnv(res.tail))
    }
  implicit def mergeLeftSome[H1, T1 <: HList, T2 <: HList](implicit inner: Merge[T1, T2]) =
    new Merge[SomeT[H1]:: T1, NoneT :: T2] {
      type Res = SomeT[H1] :: inner.Res

      def aEnv(res: Res) = ::(res.head, inner.aEnv(res.tail))
      def bEnv(res: Res) = ::(NoneT, inner.bEnv(res.tail))
    }
  implicit def mergeRightSome[T1 <: HList, H2, T2 <: HList](implicit inner: Merge[T1, T2]) =
    new Merge[NoneT :: T1, SomeT[H2]:: T2] {
      type Res = SomeT[H2] :: inner.Res

      def aEnv(res: Res) = ::(NoneT, inner.aEnv(res.tail))
      def bEnv(res: Res) = ::(res.head, inner.bEnv(res.tail))
    }
  implicit def mergeBothH[H, T1 <: HList, T2 <: HList](implicit inner: Merge[T1, T2]) =
    new Merge[SomeT[H]:: T1, SomeT[H]:: T2] {
      type Res = SomeT[H] :: inner.Res

      def aEnv(res: Res) = ::(res.head, inner.aEnv(res.tail))
      def bEnv(res: Res) = ::(res.head, inner.bEnv(res.tail))
    }
  implicit def mergeHNilRest[T2 <: HList] =
    new Merge[HNil, T2] {
      type Res = T2

      def aEnv(res: Res) = HNil
      def bEnv(res: Res) = res
    }
  implicit def mergeRestHNil[T1 <: HList] =
    new Merge[T1, HNil] {
      type Res = T1

      def aEnv(res: Res) = res
      def bEnv(res: Res) = HNil
    }

  // Evidence that an environment has a variable of the correct type on top. Also
  // a helper to create the right kind of environment the body of a lambda expects.
  trait Expects[T, E <: HList] {
    type Res <: HList
    def create(t: T, e: Res): E
  }
  implicit def expectsNothing[T] = new Expects[T, HNil] {
    type Res = HNil
    def create(t: T, e: HNil): HNil = e
  }
  implicit def expectsNone[T, R <: HList] = new Expects[T, NoneT :: R] {
    type Res = R
    def create(t: T, e: R): NoneT :: R = ::(NoneT, e)
  }
  implicit def expectsT[T, R <: HList] = new Expects[T, SomeT[T]:: R] {
    type Res = R
    def create(t: T, r: R): SomeT[T] :: R = ::(SomeT(t), r)
  }

  // THE IMPORTANT TYPE-SAFE CONSTRUCTION PART STARTS HERE //

  // The basic expression type for an expression of type T.
  // F denotes an HList of the free variable types.
  sealed trait Exp[F <: HList, T]

  // Literal integer, doesn't introduce any free vars
  case class C(i: Int) extends Exp[HNil, Int]

  // Constructors of the remaining Exp subtypes are separated from the actual case classes holding the data
  // for syntactic reasons.

  // Addition
  // merges free variable lists from both arguments
  def Add[A <: HList, B <: HList](e1: Exp[A, Int], e2: Exp[B, Int])(implicit merge: Merge[A, B]): Exp[merge.Res, Int] = AddExp(e1, e2, merge)
  // variable access, introduce a new free variable at the position indicated
  def Var[N <: Nat, T](implicit at: At[N, T]): Exp[at.Res, T] = VarExp(at)

  // Lambda constructor, T is the argument type, U the result type, uses Expects to make sure
  // the body expects the correct type of variable on top of its free variable stack
  def Lam[T] =
    // pseudo partial type application syntax
    new {
      def apply[U, B <: HList](body: Exp[B, U])(implicit e: Expects[T, B]): Exp[e.Res, T ⇒ U] = LamExp(body, e)
    }

  // Function application. Merges free variable lists for both arguments
  def App[T, U, A <: HList, B <: HList](f: Exp[A, T ⇒ U], a: Exp[B, T])(implicit merge: Merge[A, B]): Exp[merge.Res, U] = AppExp(f, a, merge)

  // THE IMPORTANT TYPE-SAFE CONSTRUCTION PART ENDS HERE //

  // the actual case classes holding the data used by the above constructors
  case class AddExp[A <: HList, B <: HList, R <: HList](e1: Exp[A, Int], e2: Exp[B, Int], merge: Merge[A, B] { type Res = R }) extends Exp[R, Int]
  case class VarExp[N <: Nat, T, R <: HList](at: At[N, T] { type Res = R }) extends Exp[R, T]
  case class LamExp[T, U, B <: HList, R <: HList](body: Exp[B, U], e: Expects[T, B] { type Res = R }) extends Exp[R, T ⇒ U]
  case class AppExp[T, U, A <: HList, B <: HList, R <: HList](f: Exp[A, T ⇒ U], a: Exp[B, T], merge: Merge[A, B] { type Res = R }) extends Exp[R, U]

  // top-level eval: works only on expression with no free variables
  def eval[T](e: Exp[HNil, T]): T = eval(HNil, e)

  // we don't define the eval's directly in the pattern match, because pattern
  // matching is known to be unsound in Scala in lots of places...
  def eval[E <: HList, T](env: E, e: Exp[E, T]): T =
    e match {
      case c: C                     ⇒ evalC(c)
      case a: AddExp[_, _, E]       ⇒ evalAddExp(env, a)
      case l: LamExp[_, _, _, E]    ⇒ evalLamExp(env, l)
      case a: AppExp[_, _, _, _, E] ⇒ evalAppExp(env, a)
      case v: VarExp[_, _, _]       ⇒ evalVarExp(env, v)
    }

  def evalC(c: C): Int = c.i
  def evalAddExp[E <: HList, A <: HList, B <: HList](env: E, add: AddExp[A, B, E]): Int =
    eval(add.merge.aEnv(env), add.e1) + eval(add.merge.bEnv(env), add.e2)
  def evalLamExp[T, U, B <: HList, E <: HList](env: E, lam: LamExp[T, U, B, E]): T ⇒ U =
    x ⇒ eval(lam.e.create(x, env), lam.body)
  def evalAppExp[T, U, A <: HList, B <: HList, E <: HList](env: E, app: AppExp[T, U, A, B, E]): U =
    eval(app.merge.aEnv(env), app.f)(eval(app.merge.bEnv(env), app.a))
  def evalVarExp[N <: Nat, T, E <: HList](env: E, varExp: VarExp[N, T, E]): T =
    varExp.at(env)
}

object TestExtended extends App {
  import Extended._

  def var0 = Var[_0, Int] // Exp[SomeT[Int] :: HNil, Int]
  def var1 = Var[_1, Int] // Exp[NoneT :: SomeT[Int] :: HNil, Int]
  def myApp = Lam[Int ⇒ Int](Lam[Int](App(Var[_1, Int ⇒ Int], var0))) // Exp[HNil, (Int => Int) => Int => Int]
  def identityInt = Lam(var0) // Exp[HNil, Int => Int]
  def constInt = Lam[Int](Lam[Int](var1)) // Exp[HNil, Int => Int => Int]
  def add1 = Lam[Int](Add(var0, C(1))) // Exp[HNil, Int => Int]
  def unfinishedAdd = Add(C(1), var0) // Exp[SomeT[Int] :: HNil, Int]
  def testApp = App(Lam(var0), C(1)) // Exp[HNil, Int]

  // doesn't work, as it contains free variables
  // eval(unfinishedAdd)
}