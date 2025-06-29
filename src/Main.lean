import MyMathProject.TCL.src.Multihole
import MyMathProject.TCL.src.TCL1

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

-- 修正 #1: 使用 `open` 来更清晰地管理命名空间
-- 这将 TCL.MultiHole.Session 中的所有公共定义引入当前作用域
open TCL.MultiHole.Session
open TCL.Interactive.Session (instToStringStatement) -- 只引入 ToString 实例

-- ## 1. 类型桥接 (Type Bridge)
-- 这是连接两个系统的关键粘合剂。虽然两个文件中的 `Statement`
-- 结构相同，但它们在Lean的类型系统中是不同的类型，因为它们位于
-- 不同的命名空间。我们需要一个显式的转换函数。

-- 将系统A的 Predicate 转换为系统B的 Predicate
def convertPredicate (p : TCL.MultiHole.Predicate) : TCL.Interactive.Predicate :=
  match p with
  | .Be => .Be
  | .Rewrite => .Rewrite

-- 将系统A的 Statement 递归转换为系统B的 Statement
partial def convertStatement (s_A : TCL.MultiHole.Statement) : TCL.Interactive.Statement :=
  match s_A with
  | .noun n => .noun n
  | .formula subj pred obj =>
      .formula (convertStatement subj) (convertPredicate pred) (convertStatement obj)
  | .naming name body => .naming (convertStatement name) (convertStatement body)
  | .seq s1 s2 => .seq (convertStatement s1) (convertStatement s2)

-- ## 2. 统一的交互模块
-- 我们需要一个新的交互逻辑，它可以解析系统B支持的更多语句格式。

/--
一个统一的解析器，可以处理多种用户输入格式：
- `'simple_noun'`
- `'[name, body]'` (来自系统A)
- `'(subject -> object)'` (来自系统B)
-/
def combinedParser (input : String) : IO TCL.Interactive.Statement := do
  let trimmed := input.trim
  if trimmed.startsWith "(" && trimmed.endsWith ")" then
    let inner := trimmed.drop 1 |>.dropRight 1
    match inner.splitOn "->" with
    | [s, o] => return .formula (.noun s.trim) .Rewrite (.noun o.trim)
    | _ =>
      IO.println s!"[Parser Warning] Invalid formula format. Treating as simple noun."
      return .noun trimmed
  else if trimmed.startsWith "[" && trimmed.endsWith "]" then
    let inner := trimmed.drop 1 |>.dropRight 1
    match inner.splitOn "," with
    | [n, b] => return .naming (.noun n.trim) (.noun b.trim)
    | _ =>
      IO.println s!"[Parser Warning] Invalid naming format. Treating as simple noun."
      return .noun trimmed
  else
    return .noun trimmed

/--
为多洞感知定制的答案收集循环，使用我们新的 `combinedParser`。
它返回一个 `Answers` 哈希图，但其中的 Statement 是系统B的类型。
-/
partial def askForAnswersCombined (ids : List TCL.MultiHole.HoleId) (answers : Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) : IO (Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) := do
  match ids with
  | [] => return answers
  | id :: rest =>
    IO.println s!"\nPlease provide a statement for <HOLE {id}>"
    IO.println "Supported formats: 'noun', '[name, body]', or '(subject -> object)'"
    IO.print "> "
    let stdin ← IO.getStdin
    let userInput ← stdin.getLine
    let statement ← combinedParser userInput.trim
    askForAnswersCombined rest (answers.insert id statement)


-- ## 3. 主执行函数 `main`

def main : IO Unit := do
  IO.println "================================================="
  IO.println "   Combined Multi-Hole Perception & Computation"
  IO.println "================================================="

  -- 步骤 1: 定义一个复杂的多洞模板。
  -- 这个模板的结构是 `(<HOLE 0> • (<HOLE 0> → <HOLE 1>))`
  -- 这是一个典型的 "前提 • (前提 → 结论)" 结构，等待被填充。
  let template : TCL.MultiHole.MultiContext :=
    .seq
      (.hole 0)
      (.formula (.hole 0) TCL.MultiHole.Predicate.Rewrite (.hole 1))

  IO.println s!"[Frontend] A multi-hole template has been defined:"
  -- `prettyPrint` 来自 `open TCL.MultiHole.Session`
  IO.println s!"  Template: {prettyPrint template}"

  -- 步骤 2: 使用系统A的机制感知洞。
  -- `getHoleIds` 也来自 `TCL.MultiHole.Session`
  let holeIds := (TCL.MultiHole.Session.getHoleIds template).eraseDup.insertionSort (· ≤ ·)
  IO.println s!"[Frontend] System perceives {holeIds.length} unique holes: {holeIds}"
  IO.println "-------------------------------------------------"

  -- 步骤 3: 使用统一的交互界面收集所有答案。
  IO.println "[Frontend] Starting to collect answers for all holes..."
  -- 修正 #2: 使用 Std.HashMap.empty 或指定容量
  let finalAnswersB ← askForAnswersCombined holeIds (Std.HashMap.emptyWithCapacity)

  -- 更优的方案：重写 `fill` 函数以直接处理系统B的答案
  let rec fillCombined (mc : TCL.MultiHole.MultiContext) (answers : Std.HashMap TCL.MultiHole.HoleId TCL.Interactive.Statement) : Option TCL.Interactive.Statement :=
    match mc with
    | .hole id => answers[id]?
    | .const s => some (convertStatement s) -- 常量需要转换
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

  -- 步骤 4: 填充模板，直接生成一个系统B的 `Statement`。
  match fillCombined template finalAnswersB with
  | none =>
    IO.println "❌ Error: Failed to fill the template. A required answer was missing."
  | some assembledStatement =>
    IO.println "✅ Success! Template filled."
    -- 修正 #3: 使用 `have` 显式引入实例，确保编译器能找到它
    have : ToString TCL.Interactive.Statement := instToStringStatement
    IO.println s!"[Object Level] Assembled statement: {assembledStatement}"

    -- 步骤 5: 将组装好的语句送入系统B的计算引擎。
    IO.println "\n[Backend] Wrapping statement in Gamma context and sending to evaluation engine..."
    -- 使用全名确保无歧义
    let worldToEvaluate : TCL.Interactive.Statement := .naming (.noun TCL.Interactive.Noun.gamma) assembledStatement
    IO.println s!"  Engine Input: {worldToEvaluate}"

    -- 执行计算
    let finalWorld := TCL.Interactive.eval worldToEvaluate

    -- 步骤 6: 展示最终结果。
    IO.println "\n[Backend] Evaluation complete."
    IO.println s!"  Engine Output (Final State): {finalWorld}"
    IO.println "================================================="

end CombinedSystem

-- 要运行这个集成的交互式会话，请取消下面这行代码的注释。
#eval CombinedSystem.main
