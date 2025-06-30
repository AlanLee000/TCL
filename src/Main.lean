import MyMathProject.TCL.src.Multihole
import MyMathProject.TCL.src.TCL1
import Lean.Parser -- 引入 Lean 的解析器库
import Lean.Elab.Command -- 1. 引入 Command Elab Monad

namespace CombinedSystem.Parser
open Lean Parser
open Lean.Elab.Command -- 允许直接使用 CommandElabM
open TCL.Interactive

-- `declare_syntax_cat`, `syntax` 规则和 `elabStatement` 保持完全不变
declare_syntax_cat tcl_statement
syntax ident : tcl_statement
syntax "(" tcl_statement "->" tcl_statement ")" : tcl_statement
syntax "[" tcl_statement "," tcl_statement "]" : tcl_statement
syntax tcl_statement:66 " • " tcl_statement:65 : tcl_statement
syntax "(" tcl_statement ")" : tcl_statement

partial def elabStatement : Syntax → Except String Statement
  | `(tcl_statement| $n:ident) =>
    return .noun n.getId.toString
  | `(tcl_statement| ( $s:tcl_statement -> $o:tcl_statement )) => do
    let s' ← elabStatement s
    let o' ← elabStatement o
    return .formula s' .Rewrite o'
  | `(tcl_statement| [ $n:tcl_statement , $b:tcl_statement ]) => do
    let n' ← elabStatement n
    let b' ← elabStatement b
    return .naming n' b'
  | `(tcl_statement| $s1:tcl_statement • $s2:tcl_statement) => do
    let s1' ← elabStatement s1
    let s2' ← elabStatement s2
    return .seq s1' s2'
  | `(tcl_statement| ( $s:tcl_statement )) => elabStatement s
  | _ => Except.error "未知或无效的语句语法"


-- 4. 创建一个顶层函数来运行整个解析流程。
--    *** 这是发生变化的地方 ***
def parseStatement (input : String) : CommandElabM (Option Statement) := do
  -- 2. 现在 getEnv 可以工作了，因为它在 CommandElabM 中
  let env ← getEnv
  -- runParserCategory 是纯函数，它不关心在哪个监视中被调用
  match Parser.runParserCategory env `tcl_statement input with
  | Except.error e =>
    -- 3. IO 操作被自动提升到 CommandElabM 中
    IO.println s!"[Parser Error] {e}"
    return none
  | Except.ok stx =>
    match elabStatement stx with
    | Except.error e =>
      IO.println s!"[Elaboration Error] {e}"
      return none
    | Except.ok stmt =>
      return some stmt

end CombinedSystem.Parser
/-!
# 多洞感知计算系统 (Combined System) - 修正版

本文件整合了“多洞感知机制”(系统A) 和“三元组语境语言计算引擎”(系统B)。

工作流程:
1.  **定义元模板 (来自系统A)**: 使用 `MultiContext` 定义一个带有多个“洞”的复杂问题模板。
2.  **感知与交互 (来自系统A)**: 使用 `getHoleIds` 发现所有洞，并通过交互式会话向用户收集所有答案。
3.  **类型桥接 (核心集成)**: 将系统A的 `Statement` 和 `Predicate` 类型转换为系统B中功能等价的类型。这是模块化集成的关键。
4.  **组装对象语句 (来自系统A)**: 使用 `fill` 函数将答案填入模板，生成一个完整的、复杂的语句。
5.  **执行计算 (来自系统B)**: 将组装好的语句送入系统B强大的 `eval` 引擎进行归约。
6.  **展示最终结果**: 输出计算后的最终稳定状态。

这个架构展示了一个强大的模式：
- **系统A (MultiHole)** 作为灵活的 **“知识获取前端”**。
- **系统B (TCL1)** 作为强大的 **“形式化计算后端”**。
-/
namespace CombinedSystem

-- ## 1. 命名空间管理 (核心修正)
-- 只从 MultiHole.Session 导入我们需要的函数，避免名称冲突
open TCL.MultiHole.Session (prettyPrint getHoleIds)
-- 同样，只从 Interactive.Session 导入 ToString 实例
open TCL.Interactive.Session (instToStringStatement)
-- 导入我们新的解析器模块和 CommandElabM
open CombinedSystem.Parser
open Lean.Elab.Command

-- ## 2. 类型桥接 (无变化)
def convertPredicate (p : TCL.MultiHole.Predicate) : TCL.Interactive.Predicate :=
  match p with
  | .Be => .Be
  | .Rewrite => .Rewrite

partial def convertStatement (s_A : TCL.MultiHole.Statement) : TCL.Interactive.Statement :=
  match s_A with
  | .noun n => .noun n
  | .formula subj pred obj =>
      .formula (convertStatement subj) (convertPredicate pred) (convertStatement obj)
  | .naming name body => .naming (convertStatement name) (convertStatement body)
  | .seq s1 s2 => .seq (convertStatement s1) (convertStatement s2)

-- ## 3. 交互模块 (无变化)
-- (askForAnswersCombined 函数现在可以正确地解析名称，因为歧义已消除)
partial def askForAnswersCombined (ids : List TCL.MultiHole.HoleId) (answers : Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) : CommandElabM (Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) := do
  match ids with
  | [] => return answers
  | id :: rest =>
    IO.println s!"\nPlease provide a statement for <HOLE {id}>"
    IO.println "Supported formats: 'noun', '[name, body]', '(subject -> object)', 's1 • s2'"
    IO.print "> "
    let stdin ← IO.getStdin
    let userInput ← stdin.getLine
    -- 歧义已解决，这里将明确调用 CombinedSystem.Parser.parseStatement
    match ← parseStatement userInput.trim with
    | none =>
      IO.println "Invalid input. Please try again."
      askForAnswersCombined (id :: rest) answers
    | some statement =>
      askForAnswersCombined rest (answers.insert id statement)

-- ## 4. 主执行函数 `main` (修正了 HashMap 的创建)
def main : CommandElabM Unit := do
  IO.println "================================================="
  IO.println "   Combined Multi-Hole Perception & Computation"
  IO.println "================================================="

  let template : TCL.MultiHole.MultiContext :=
    .seq
      (.hole 0)
      (.formula (.hole 0) TCL.MultiHole.Predicate.Rewrite (.hole 1))

  IO.println s!"[Frontend] A multi-hole template has been defined:"
  -- `prettyPrint` 和 `getHoleIds` 现在可以安全使用
  IO.println s!"  Template: {prettyPrint template}"

  let holeIds := (getHoleIds template).eraseDup.insertionSort (· ≤ ·)
  IO.println s!"[Frontend] System perceives {holeIds.length} unique holes: {holeIds}"
  IO.println "-------------------------------------------------"

  IO.println "[Frontend] Starting to collect answers for all holes..."
  -- 使用 `{}` 来创建空的 HashMap，修复了弃用警告
  let finalAnswersB ← askForAnswersCombined holeIds {}

  let rec fillCombined (mc : TCL.MultiHole.MultiContext) (answers : Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) : Option TCL.Interactive.Statement :=
    match mc with
    | .hole id => answers[id]?
    | .const s => some (convertStatement s)
    | .formula s p o => do
      let s' ← fillCombined s answers
      let o' ← fillCombined o answers
      return .formula s' (convertPredicate p) o'
    | .naming n b => do
      let n' ← fillCombined n answers
      let b' ← fillCombined b answers
      return .naming n' b'
    | .seq c1 c2 => do
      let s1' ← fillCombined c1 answers
      let s2' ← fillCombined c2 answers
      return .seq s1' s2'

  IO.println "\n-------------------------------------------------"
  IO.println "[Bridge] All answers collected. Attempting to fill the template..."

  match fillCombined template finalAnswersB with
  | none =>
    IO.println "❌ Error: Failed to fill the template. A required answer was missing."
  | some assembledStatement =>
    IO.println "✅ Success! Template filled."
    have : ToString TCL.Interactive.Statement := instToStringStatement
    IO.println s!"[Object Level] Assembled statement: {assembledStatement}"

    IO.println "\n[Backend] Wrapping statement in Gamma context and sending to evaluation engine..."
    let worldToEvaluate : TCL.Interactive.Statement := .naming (.noun TCL.Interactive.Noun.gamma) assembledStatement
    IO.println s!"  Engine Input: {worldToEvaluate}"

    let finalWorld := TCL.Interactive.eval worldToEvaluate

    IO.println "\n[Backend] Evaluation complete."
    IO.println s!"  Engine Output (Final State): {finalWorld}"
    IO.println "================================================="

end CombinedSystem

-- 现在可以正确工作了
#eval CombinedSystem.main
