type PMUnit = -1 | 1

case class Term(a: -1 | 1, x: Int):
  def unary_- = Term(if a == 1 then -1 else 1, x)

enum Constraint:
  case AddConstr(val l: Term, val r: Term, val d: Int)
  case BndConstr(val t: Term, val d: Int)
import Constraint.*

extension (self: AddConstr)
  def otherTerm(t: Term): Option[(Term, Int)] = self match
    // if self is -l + r2 <= d2 or r2 - l <= d2 then return (r2, d2)
    case AddConstr(l, r, d) =>
      if l == t then Some((r, d))
      else if r == t then Some((l, d))
      else None

extension (self: BndConstr)
  def boundFor(t: Term): Option[Int] = self match
    // if self is -l <= d2 then return (r2, d2)
    case BndConstr(t1, d) =>
      if t1 == t then Some(d)
      else None

def combine(
    as: List[AddConstr],
    bs: List[BndConstr],
    c: AddConstr
): (List[AddConstr], List[BndConstr]) =
  val AddConstr(l, r, d) = c
  var newAs: List[AddConstr] = List.empty
  var newBs: List[BndConstr] = List.empty
  val ls = as.flatMap(_.otherTerm(-l))
  val rs = as.flatMap(_.otherTerm(-r))
  // Rule 1
  newAs ++= ls.map((l2, d2) => AddConstr(l2, r, d + d2))
  newAs ++= rs.map((r2, d2) => AddConstr(l, r2, d + d2))
  // Rule 2
  newAs ++= ls.flatMap((l2, d2) =>
    rs.map((r2, d3) => AddConstr(l2, r2, d + d2 + d3))
  )
  val lds = bs.flatMap(_.boundFor(-l))
  val rds = bs.flatMap(_.boundFor(-r))
  // Rule 3
  newBs ++= lds.map(d2 => BndConstr(r, d + d2))
  newBs ++= rds.map(d2 => BndConstr(l, d + d2))
  // Rule 4
  newBs ++= lds.flatMap(d2 => rs.map((r2, d3) => BndConstr(r2, d + d2 + d3)))
  newBs ++= rds.flatMap(d2 => ls.map((l2, d3) => BndConstr(l2, d + d2 + d3)))
  // Rule 5
  newBs ++= ls
    .filter((l2, d2) => l2 == l)
    .map((l2, d2) => BndConstr(l, (d + d2) / 2))
  newBs ++= rs
    .filter((r2, d2) => r2 == r)
    .map((r2, d2) => BndConstr(r, (d + d2) / 2))
  // Rule 6
  newBs ++= ls.flatMap((l2, d2) =>
    rs.filter((r2, d3) => r2 == l2)
      .map((r2, d3) => BndConstr(l2, (d + d2 + d3) / 2))
  )
  (newAs, newBs)
