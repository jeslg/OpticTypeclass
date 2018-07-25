package org.hablapps.statelesser
package test

import scalaz.{ Lens => _, _ }, Scalaz._
import monocle._, monocle.state.all._, macros.GenLens, function.all._

object UniversityTypeclass extends App {

  // In this file, we implement the university example using a typeclass that
  // supplies optics. There are two approaches to do so. Firstly we go for the
  // classic approach, where the nexus between algebras is itself an optic.
  // Secondly, we take the `ListP` approach, where the nexus between algebras is
  // a function that generates a list of nested algebras.

  /*****************************/
  /* 1st approach, basic style */
  /*****************************/

  /* data layer */

  // This is the typeclass `University`, which supplies optics to deal with its
  // inner components. Not actually the classic typeclass pattern, we use case
  // classes foreseeing integration with Shapeless. Anyway, the pattern is
  // clear: we use a lens for a single-valued field. We use traversals for
  // multiple-valued fields. In this situation, the multiple-valued field
  // happens to be the nexus with the nested `Department` algebra.
  
  case class University[Univ, Dep: Department](
    name: Lens[Univ, String],
    comm: Lens[Univ, Int],
    deps: Traversal[Univ, Dep])

  object University {
    def apply[Univ, Dep](implicit 
        ev: University[Univ, Dep]): University[Univ, Dep] = 
      ev
  }

  case class Department[Dep](budg: Lens[Dep, Int])

  object Department {
    def apply[Dep](implicit ev: Department[Dep]): Department[Dep] = ev
  }

  /* logic */
 
  // We provide a class to encapsulate the logic. It requires evidences of the
  // data layer typeclasses. Then, we can implement the logic by composing the
  // packaged optics and invoking their interfaces. Here we can see that we are
  // abstracted away from the datatype representation, which turns out to be
  // pretty cool (usual with typeclasses).

  class Logic[Univ: University[?, Dep], Dep: Department] {

    private val univ = University[Univ, Dep]
    private val dep  = Department[Dep]
    import univ._, dep._
    
    def getUnivName: State[Univ, String] = name.extract 

    def upcUnivName: State[Univ, Unit] = name.mod_(_.toUpperCase)

    def getUnivBudg: State[Univ, Int] = 
      gets((deps composeLens budg).getAll(_).sum)

    def doubleUnivBudg: State[Univ, Unit] = 
      modify((deps composeLens budg).modify(_ * 2))
  }

  /* interpretation */

  // Now, we can specify the datatypes that we want to work with. Of course, we
  // provide typeclass instances for them.

  case class SUniversity(
    name: String, 
    community: Int, 
    departments: List[SDepartment])

  object SUniversity {
    implicit val uni: University[SUniversity, SDepartment] =
      University(
        GenLens[SUniversity](_.name),
        GenLens[SUniversity](_.community),
        GenLens[SUniversity](_.departments) composeTraversal each)
  }

  case class SDepartment(budget: Int)

  object SDepartment {
    implicit val dep: Department[SDepartment] = 
      Department(GenLens[SDepartment](_.budget))
  }

  val logic = new Logic[SUniversity, SDepartment] 

  /* execution */

  import logic._

  val math = SDepartment( 80000)
  val cs   = SDepartment(100000)
  val urjc = SUniversity("urjc", 7500, List(math, cs))

  println(upcUnivName.exec(urjc))
  println((doubleUnivBudg >> getUnivBudg)(urjc))


  /*****************************/
  /* 2nd approach, ListP style */
  /*****************************/
 
  /* data layer */

  // Here we can find a remarkable difference. Instead of providing a traversal
  // as nexus, this typeclass uses a function from `Univ` to a list of instances
  // of the `Department` algebra. We use the same `Department` algebra from the
  // 1st approach. Notice that they are parameterized with the same `Univ`
  // state. I mean, these instances should know how to update the whole `Univ`
  // so they are somehow pointing at a particular department.
  
  case class University2[Univ](
    name: Lens[Univ, String],
    comm: Lens[Univ, Int],
    deps: Univ => List[Department[Univ]])

  /* logic */

  // The logic is affected by the data layer changes. We are no longer composing
  // optics, since they all generate programs that update the `Univ` directly.
  // Instead, we use standard combinators such as `traverse` to make things
  // work. Maybe we could search for better combinators, but this version is
  // quite readable, although the `get(deps) >>=` is a little bit annoying to
  // me.

  class Logic2[Univ](univ: University2[Univ]) {
    import univ._
    
    def getUnivName2: State[Univ, String] = name.extract 

    def upcUnivName2: State[Univ, Unit] = name.mod_(_.toUpperCase)

    def getUnivBudg2: State[Univ, Int] = 
      gets(deps) >>= (_.traverse(_.budg.extract).map(_.sum))

    def doubleUnivBudg2: State[Univ, Unit] =
      gets(deps) >>= (_.traverse(_.budg.mod_(_ * 2)).void)
  }

  /* interpretation */

  // We need to supply an instance of the function that acts as nexus. This code
  // is not much nice, since it contain a side effect: `toDepMap(u)(i).budget`
  // where we assume that the map is defined for `i`. It seems reasonable, if we
  // take into account that we are generating the list of instances from a value
  // where it is actually defined. If we get the list of department algebras and
  // modify the state, we should reload them before achieving a further
  // modification. Otherwise intermediate updates could get lost. We still need
  // to check laws and assert that both versions are equivalent.

  val deps2: SUniversity => List[Department[SUniversity]] = { univ => 
    def toDepMap(u: SUniversity) = u.departments.zipWithIndex.map(_.swap).toMap
    toDepMap(univ).map { case (i, v) => 
      Department(Lens[SUniversity, Int](
        u => toDepMap(u)(i).budget)(
        b => u => u.copy(departments = 
          toDepMap(u).updated(i, v.copy(b)).values.toList)))
    }.toList
  }

  val univ2 = University2(
    GenLens[SUniversity](_.name),
    GenLens[SUniversity](_.community),
    deps2)

  val logic2 = new Logic2(univ2)

  /* execution */

  import logic2._

  println(upcUnivName2.exec(urjc))
  println((doubleUnivBudg2 >> getUnivBudg2)(urjc))
}

