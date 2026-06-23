package wildcat.isasim

import scala.collection.mutable.HashMap
import scala.collection.mutable.Map
import java.lang.Integer.compareUnsigned
import java.lang.Long.parseLong
import scala.io.Source.fromFile

object Profiler {
  def load(path: String): Profiler = {
    val rx = """([0-9a-fA-F]+)\s+[tTwWrR]\s+(\S+)""".r
    val syms = fromFile(path).getLines()
      .collect { case rx(a, n) => (parseLong(a, 16).toInt, n) }
      .toArray
      .sortWith((x, y) => compareUnsigned(x._1, y._1) < 0)
    new Profiler(syms.map(_._1), syms.map(_._2))
  }
}

class Profiler(addr: Array[Int], name: Array[String]) {
  val count = new Array[Long](addr.length)
  // callee name -> (calling function name -> number of calls)
  val callers = HashMap[String, Map[String, Long]]()

  def recordCall(callee: String, retPc: Int): Unit = {
    val byCaller = callers.getOrElseUpdate(callee, HashMap[String, Long]().withDefaultValue(0L))
    byCaller(nameOf(retPc)) += 1
  }

  // greatest symbol whose address <= pc (unsigned)
  def idx(pc: Int): Int = {
    var lo = 0; var hi = addr.length - 1; var res = 0
    while (lo <= hi) {
      val mid = (lo + hi) >>> 1
      if (compareUnsigned(addr(mid), pc) <= 0) { res = mid; lo = mid + 1 }
      else hi = mid - 1
    }
    res
  }
  def sample(pc: Int): Unit = count(idx(pc)) += 1
  def nameOf(pc: Int): String = name(idx(pc))
  def entryAddrs(names: Set[String]): Set[Int] =
    names.flatMap(n => addr.indices.find(name(_) == n).map(addr(_)))

  def report(top: Int): Unit = {
    val total = count.sum.max(1L)

    Console.err.println()
    Console.err.println(f"=== Hot functions (top $top by sampled PC) ===")
    Console.err.println(f"""${"share"}%7s  ${"samples"}%12s  symbol""")
    count.zipWithIndex.sortBy(-_._1).take(top).foreach { case (c, i) =>
      if (c > 0) Console.err.println(f"${100.0 * c / total}%6.2f%%  $c%12d  ${name(i)}")
    }

    if (callers.nonEmpty) {
      Console.err.println()
      Console.err.println("=== Call sites (immediate caller of tracked functions) ===")
      callers.toSeq.sortBy(_._1).take(top).foreach { case (callee, byCaller) =>
        Console.err.println(f"$callee  (${byCaller.values.sum} calls)")
        byCaller.toSeq.sortBy(-_._2).take(top).foreach { case (n, c) =>
          Console.err.println(f"  $n%-30s $c%8d")
        }
      }
    }
  }
}
