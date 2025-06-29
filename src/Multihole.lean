import Std.Data.HashMap
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic -- List.eraseDup 位于此

/-!
# 多洞感知机制 (Multi-Hole Perception Mechanism) - 交互式实例 (最终修正版)

本文件实现了“多洞感知机制”的交互式演示。
它使用一个完全可计算的工作流来发现和处理模板中的空缺，
解决了非计算性依赖的问题。

这个模块是完全自包含的，可以直接运行。
-/
namespace TCL.MultiHole

-- ## 1. 核心类型定义 (自包含)
-- ... (这部分不变) ...
open Std

inductive Predicate where
  | Be
  | Rewrite
  deriving Repr, Inhabited, BEq

instance : ToString Predicate where
  toString
    | .Be      => "be"
    | .Rewrite => "→"

inductive Statement where
  | noun (n : String)
  | formula (s : Statement) (p : Predicate) (o : Statement)
  | naming (n : Statement) (b : Statement)
  | seq (s1 : Statement) (s2 : Statement)
  deriving Repr, Inhabited, BEq

notation:50 "[" a ", " b "]" => Statement.naming a b
infixr:65 " • " => Statement.seq

partial instance : ToString Statement where
  toString s :=
    let rec go (s : Statement) : String :=
      match s with
      | .noun n => n
      | .formula subj pred obj => s!"({go subj}, {toString pred}, {go obj})"
      | .naming name body => s!"[{go name}, {go body}]"
      | .seq s1 s2 => s!"{go s1} • {go s2}"
    go s

def noun (n : String) : Statement := .noun n
def form (s : Statement) (p : Predicate) (o : Statement) : Statement := .formula s p o
def be : Predicate := .Be
def rewrite : Predicate := .Rewrite

-- ## 2. 多洞感知机制的核心实现
-- ... (这部分不变) ...
abbrev HoleId := Nat

inductive MultiContext where
  | hole (id : HoleId)
  | const (s : Statement)
  | formula (s : MultiContext) (p : Predicate) (o : MultiContext)
  | naming (n : MultiContext) (b : MultiContext)
  | seq (c1 : MultiContext) (c2 : MultiContext)
  deriving Repr

abbrev Answers := HashMap HoleId Statement

def MultiContext.fill (mc : MultiContext) (answers : Answers) : Option Statement :=
  match mc with
  | .hole id => answers[id]?
  | .const s => some s
  | .formula s p o => do
    let s' ← s.fill answers
    let o' ← o.fill answers
    return .formula s' p o'
  | .naming n b => do
    let n' ← n.fill answers
    let b' ← b.fill answers
    return .naming n' b'
  | .seq c1 c2 => do
    let s1' ← c1.fill answers
    let s2' ← c2.fill answers
    return .seq s1' s2'

-- ==================================================================
-- ## 3. 交互式会话实现 (修正部分)
-- ==================================================================
namespace Session

/--
**修正**: 此函数现在返回一个 `List HoleId`，它是完全可计算的。
它通过列表拼接 (`++`) 来收集所有出现的 `HoleId`。
-/
def getHoleIds (mc : MultiContext) : List HoleId :=
  match mc with
  | .hole id => [id]
  | .const _ => []
  | .formula s _ o => getHoleIds s ++ getHoleIds o
  | .naming n b => getHoleIds n ++ getHoleIds b
  | .seq c1 c2 => getHoleIds c1 ++ getHoleIds c2

-- `prettyPrint`, `parseStatement`, `askForAnswers` 函数保持不变
def prettyPrint (mc : MultiContext) : String :=
  let rec go (mc : MultiContext) : String :=
    match mc with
    | .hole id => s!"<HOLE {id}>"
    | .const s => toString s
    | .formula s p o => s!"({go s}, {toString p}, {go o})"
    | .naming n b => s!"[{go n}, {go b}]"
    | .seq c1 c2 => s!"{go c1} • {go c2}"
  go mc

def parseStatement (input : String) : IO Statement := do
  let trimmed := input.trim
  if trimmed.startsWith "[" && trimmed.endsWith "]" then
    let inner := trimmed.drop 1 |>.dropRight 1
    match inner.splitOn "," with
    | [name, body] => return .naming (noun name.trim) (noun body.trim)
    | _ =>
      IO.println s!"[Parser Error] Invalid naming format. Treating as simple noun."
      return noun trimmed
  else
    return noun trimmed

partial def askForAnswers (ids : List HoleId) (answers : Answers) : IO Answers := do
  match ids with
  | [] => return answers
  | id :: rest =>
    IO.println s!"\nPlease provide a statement for <HOLE {id}>"
    IO.println "Supported formats: 'some_noun' or '[name, body]'"
    IO.print "> "
    let stdin ← IO.getStdin
    let userInput ← stdin.getLine
    let statement ← parseStatement userInput.trim
    askForAnswers rest (answers.insert id statement)

/--
主程序入口：演示多洞感知的完整流程。
-/
def main : IO Unit := do
  IO.println "Welcome to the Multi-Hole Perception Session!"
  IO.println "---------------------------------------------"

  let template : MultiContext :=
    .seq
      (.naming (.hole 0) (.hole 1))
      (.formula (.hole 0) be (.const (noun "concept_A")))

  IO.println s!"[Meta-Level] A multi-hole context (a complex question) has been defined:"
  IO.println s!"  Template: {prettyPrint template}"

  -- **修正**: 使用全计算的列表操作流程
  -- 1. `getHoleIds template` 返回一个可能含重复项的列表, e.g., `[0, 1, 0]`
  -- 2. `.eraseDup` 移除重复项，得到一个无重复但顺序不定的列表, e.g., `[0, 1]`
  --    (需要 `[DecidableEq HoleId]`，`Nat` 自带)
  -- 3. `.insertionSort` 对列表排序，得到稳定顺序, e.g., `[0, 1]`
  let holeIds := (getHoleIds template).eraseDup.insertionSort (· ≤ ·)

  IO.println s!"[Meta-Level] The system perceives {holeIds.length} holes that need answers: {holeIds}"
  IO.println "---------------------------------------------"

  IO.println "[Interaction Bridge] Starting to collect answers..."
  let finalAnswers ← askForAnswers holeIds {}

  IO.println "\n---------------------------------------------"
  IO.println "[Interaction Bridge] All answers collected:"
  for (id, stmt) in finalAnswers.toList do
    IO.println s!"  - Answer for <HOLE {id}> is: {stmt}"

  IO.println "\n[Object-Level] Attempting to fill the template with the provided answers..."
  match template.fill finalAnswers with
  | some finalStatement =>
    IO.println "✅ Success! The meta-level template has been resolved into a concrete object-level statement:"
    IO.println s!"   Final Statement: {finalStatement}"
  | none =>
    IO.println "❌ Error: Failed to fill the template. A required answer was missing."

end Session
end TCL.MultiHole

-- 要运行此交互式会话，请取消下面这行代码的注释
-- #eval TCL.MultiHole.Session.main
