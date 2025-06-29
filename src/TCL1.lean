import Lean
import Mathlib.Data.Finset.Basic -- 引入 Finset 用于处理名词集合
import Mathlib.Tactic
/-!
# 三元组语境语言 (TCL) 的形式化实现

本文件实现了“三元组语境语言”的核心机制，并重点关注
其元-对象交互的能力。

实现分为三个主要部分：
1.  **核心类型**: 与之前相同，定义 `Statement`, `Predicate` 等。
2.  **上下文与填洞**: 新增 `Context` 类型来形式化“洞”，并提供 `fill` 操作。
3.  **新版归约引擎**: 重写 `reduceStep` 以利用 `Context`，实现真正的
    上下文感知重写。
4.  **交互式会话模拟**: 通过一个 `IO` 示例展示元-对象循环。
-/
namespace TCL.Interactive

-- ## 1. 核心类型定义 (与之前相同)
-- ## 1. 核心类型定义 (修正)
-- 在 Predicate 定义中添加 `deriving DecidableEq`
inductive Predicate where
  | Be
  | Rewrite
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq -- 添加 DecidableEq

abbrev Noun := String

inductive Statement where
  | noun (n : Noun)
  | formula (subject : Statement) (pred : Predicate) (object : Statement)
  | naming (name : Statement) (body : Statement)
  | seq (s1 : Statement) (s2 : Statement)
  deriving Repr, BEq, Hashable, Inhabited

notation:50 "[" a ", " b "]" => Statement.naming a b
infixr:65 " • " => Statement.seq

def be      : Predicate := .Be
def rewrite : Predicate := .Rewrite

def Noun.gamma   : Noun := "Gamma"

def noun (n : Noun) : Statement := .noun n
def form (s : Statement) (p : Predicate) (o : Statement) : Statement := .formula s p o

-- ==================================================================
-- ## 2. 上下文 (Context) 与填洞 (Fill) 的形式化
-- ==================================================================

/--
`Context` 类型精确地形式化了“一个带单个洞的语句” (`<[context,]>`)。
它的结构与 `Statement` 平行，每个可以包含子语句的构造器
都对应着一个或多个 `Context` 构造器。
-/
inductive Context where
  | hole                                -- 洞本身是最简单的上下文
  | formula_subj (c : Context) (p : Predicate) (o : Statement) -- 洞在主语位置
  | formula_obj (s : Statement) (p : Predicate) (c : Context) -- 洞在宾语位置
  | naming_name (c : Context) (body : Statement)            -- 洞在语境名位置
  | naming_body (name : Statement) (c : Context)            -- 洞在语境中心位置
  | seq_left (c : Context) (s2 : Statement)                 -- 洞在平展序列的前部
  | seq_right (s1 : Statement) (c : Context)                -- 洞在平展序列的后部
  deriving Repr

/--
`Context.fill` 函数实现了“填洞”操作。
它接受一个上下文 `c` 和一个语句 `s_fill`，然后将 `s_fill`
放入 `c` 的洞中，返回一个完整的 `Statement`。
-/
def Context.fill (c : Context) (s_fill : Statement) : Statement :=
  match c with
  | .hole => s_fill
  | .formula_subj c' p o => .formula (c'.fill s_fill) p o
  | .formula_obj s p c'  => .formula s p (c'.fill s_fill)
  | .naming_name c' b    => .naming (c'.fill s_fill) b
  | .naming_body n c'    => .naming n (c'.fill s_fill)
  | .seq_left c' s2      => .seq (c'.fill s_fill) s2
  | .seq_right s1 c'     => .seq s1 (c'.fill s_fill)

-- ==================================================================
-- ## 3. 新版归约引擎
-- ==================================================================

/--
`Redex` 结构体，用于表示一个已发现的可归约表达式。
它包含了：
- `ctx`: 红式 (redex) 在整个语句中的上下文。
- `redex`: 红式自身，即形如 `a • (a → b)` 的语句。
- `replacement`: 用于替换红式的语句，即 `b`。
-/
structure Redex where
  ctx         : Context
  redex       : Statement
  replacement : Statement
  deriving Repr

/--
`findRedex` 函数是新引擎的核心。
它以“最左-最内”的策略，深度优先地在语句中寻找第一个可归约表达式。
如果找到，它返回一个 `Redex` 结构体，包含了完成重写所需的所有信息。
-/
 def findRedex (s : Statement) : Option Redex :=
  match s with
  -- 序列是唯一可能直接成为红式的节点
  | .seq s1 s2 =>
    -- 优先级 1: 在左子节点中寻找红式 (最左)
    if let some r := findRedex s1 then
      -- 如果在 s1 中找到了红式，将其上下文包装在 seq_left 中
      some { r with ctx := .seq_left r.ctx s2 }
    -- 优先级 2: 在右子节点中寻找红式
    else if let some r := findRedex s2 then
      -- 如果在 s2 中找到了红式，将其上下文包装在 seq_right 中
      some { r with ctx := .seq_right s1 r.ctx }
    -- 优先级 3: 检查当前节点自身是否为红式 (最内)
    else match s2 with
         | .formula pred_s .Rewrite obj =>
           if s1 == pred_s then
             -- 找到了！上下文是 hole，因为 s 本身就是红式
             some ⟨.hole, s, obj⟩
           else none
         | _ => none
  -- 对于其他结构，只在它们的子节点中递归寻找
  | .naming n b =>
    if let some r := findRedex n then
      some { r with ctx := .naming_name r.ctx b }
    else if let some r := findRedex b then
      some { r with ctx := .naming_body n r.ctx }
    else none
  | .formula subj pred obj =>
    if let some r := findRedex subj then
      some { r with ctx := .formula_subj r.ctx pred obj }
    else if let some r := findRedex obj then
      some { r with ctx := .formula_obj subj pred r.ctx }
    else none
  -- 原子名词不是红式，也没有子节点
  | .noun _ => none

/-- 新版的单步归约函数，利用 `findRedex` 和 `Context.fill`。 -/
def reduceStep (s : Statement) : Option Statement :=
  match findRedex s with
  | some r => some (r.ctx.fill r.replacement) -- 找到红式，执行填洞替换
  | none   => none                          -- 未找到，无法归约

/-- 完全归约函数 (与之前相同，但依赖于新版的 reduceStep) -/
partial def reduce (s : Statement) : Statement :=
  match reduceStep s with
  | some s' => reduce s'
  | none    => s

/-- 全局求值函数 (与之前相同) -/
def eval (world : Statement) : Statement :=
  match world with
  | .naming (.noun g_name) s =>
    if g_name == Noun.gamma then
      .naming (noun Noun.gamma) (reduce s)
    else world
  | _ => world

end TCL.Interactive


-- (此处省略您提供的 TCL.Interactive 的所有定义，从 namespace TCL.Interactive 开始到 eval 结束)
-- 我将直接续写在您的代码之后

namespace TCL.Interactive.Proof
open TCL.Interactive

-- ## 1. 形式化定义归约关系

/--
**一步归约关系 `s ⟶ s'`**
当且仅当 `reduceStep s` 返回 `some s'` 时，`s` 可以一步归约为 `s'`。
这是对 `reduceStep` 函数行为的命题化。
-/
inductive ReducesTo : Statement → Statement → Prop where
  | step {s s' : Statement} : reduceStep s = some s' → ReducesTo s s'

-- 为一步归约关系定义中缀表示法
infix:80 " ⟶ " => ReducesTo

/--
**多步归约关系 `s ⟶* s'` (自反传递闭包)**
-/
inductive ReducesToStar : Statement → Statement → Prop where
  | refl (s : Statement) : ReducesToStar s s
  | step {s₁ s₂ s₃ : Statement} : (s₁ ⟶ s₂) → ReducesToStar s₂ s₃ → ReducesToStar s₁ s₃

-- 为多步归约关系定义中缀表示法
infix:80 " ⟶* " => ReducesToStar

-- ## 2. 核心引理与主定理

/--
**引理 1：一步归约的确定性 (Determinism of One-Step Reduction)**
这是整个合流性证明的基石。它断言如果一个项 `s` 能一步归约到 `s₁`，
同时也能一步归约到 `s₂`，那么 `s₁` 和 `s₂` 必须是同一个项。
这直接源于 `reduceStep` 是一个确定性函数。
-/
theorem reduction_is_deterministic (s s₁ s₂ : Statement) :
  (s ⟶ s₁) → (s ⟶ s₂) → s₁ = s₂ := by
  -- 展开 `⟶` 的定义
  rintro ⟨h_eq₁⟩ ⟨h_eq₂⟩
  -- 我们得到两个假设:
  -- h_eq₁: reduceStep s = some s₁
  -- h_eq₂: reduceStep s = some s₂
  -- 将 h_eq₁ 代入 h_eq₂
  rw [h_eq₁] at h_eq₂
  -- 现在 h_eq₂: some s₁ = some s₂
  -- `injection` 战术可以从 `some a = some b` 中推断出 `a = b`
  injection h_eq₂ with h_s₁_eq_s₂

/--
**辅助引理：多步归约的传递性 (Transitivity of `⟶*`)**
这个引理是标准配置，用于在证明中拼接归约路径。
-/
theorem transitivity (s₁ s₂ s₃ : Statement) : (s₁ ⟶* s₂) → (s₂ ⟶* s₃) → (s₁ ⟶* s₃) := by
  intro h_path₁ h_path₂
  induction h_path₁ with
  | refl => exact h_path₂
  | step h₁ h_rest ih =>
    apply ReducesToStar.step
    . exact h₁
    . exact ih h_path₂

/--
**钻石引理 (Strip Lemma)**
如果 m 能一步归约到 m₁，同时能多步归约到 m₂，
那么 m₁ 和 m₂ 必然能在一个共同的下游 m₃ 处汇合。
这个引理是证明合流性的关键步骤。
-/
theorem strip_lemma (m m₁ m₂ : Statement) :
  (m ⟶ m₁) → (m ⟶* m₂) → ∃ m₃, (m₁ ⟶* m₃) ∧ (m₂ ⟶* m₃) := by
  -- 引入两个前提假设
  intro h_m_m₁ h_path_m_m₂

  -- 对多步归约路径 `h_path_m_m₂` 进行归纳
  induction h_path_m_m₂

  -- 处理 `refl` 情况
  case refl m =>
    -- 此时 m₂ = m
    exists m₁
    exact ⟨.refl _, .step h_m_m₁ (.refl _)⟩

  -- 处理 `step` 情况，使用清晰的变量命名
  case step m' m_mid m_final h_m_to_m_mid h_path_m_mid_final ih =>
    -- 关键步骤：两条从 m 出发的一步归约
    have h_eq : m₁ = m_mid :=
      reduction_is_deterministic m' m₁ m_mid h_m_m₁ h_m_to_m_mid

    -- 替换变量
    subst h_eq

    -- 现在，我们取m₃ = m_final
    exists m_final
    apply And.intro
    . -- m₁ ⟶* m_final
      exact h_path_m_mid_final
    . -- m_final ⟶* m_final
      exact .refl _

/--
**主定理：合流性 (Confluence / Church-Rosser Property)**
对于任意从 `m` 出发的两条归约路径 `m ⟶* m₁` 和 `m ⟶* m₂`，
它们必然可以在某个 `m₃` 处汇合。
-/
theorem confluence (m m₁ m₂ : Statement) :
  (m ⟶* m₁) → (m ⟶* m₂) → ∃ m₃, (m₁ ⟶* m₃) ∧ (m₂ ⟶* m₃) := by
  intro h_path₁
  induction h_path₁ generalizing m₂
  case refl =>
    intro h_path₂
    exists m₂
    exact ⟨h_path₂, .refl _⟩

  case step m_start m_inter m_final h_step h_rest ih =>
    intro h_path_m_m₂
    -- 应用剥离引理处理两条路径：m→m_inter 和 m→*m₂
    have ⟨m₄, h_m_inter_to_m₄, h_m₂_to_m₄⟩ :=
      strip_lemma m_start m_inter m₂ h_step h_path_m_m₂
    -- 应用归纳假设处理：m_inter→*m_final 和 m_inter→*m₄
    have ⟨m₃, h_m_final_to_m₃, h_m₄_to_m₃⟩ :=
      ih m₄ h_m_inter_to_m₄
    -- 构建最终结果
    exists m₃
    apply And.intro
    · exact h_m_final_to_m₃
    · exact transitivity m₂ m₄ m₃ h_m₂_to_m₄ h_m₄_to_m₃

end TCL.Interactive.Proof

-- 检查证明是否引入了不希望的公理（如选择公理）
-- 预期输出为空，表示证明是完全构造性的。
#print axioms TCL.Interactive.Proof.confluence
-- ## 4. 交互式会话模拟
-- ==================================================================
-- 本节通过一个IO程序，模拟元-对象层面的交互循环。

namespace TCL.Interactive.Session
open TCL.Interactive -- 引入核心定义

/--
一个简单的辅助函数，用于将用户输入的字符串解析为一个 Statement。
为了简化，我们只支持两种格式：
1.  `"a"` -> `noun "a"`
2.  `"(a -> b)"` -> `(noun "a", rewrite, noun "b")`
-/
def parseUserInput (input : String) : IO Statement := do
  let trimmed := input.trim
  if trimmed.startsWith "(" && trimmed.endsWith ")" then
    let parts := trimmed.drop 1 |>.dropRight 1 |>.splitOn "->"
    match parts with
    | [s, o] => return form (noun s.trim) rewrite (noun o.trim)
    | _ =>
      IO.println s!"[Parser Error] Invalid formula format. Use '(subject -> object)'. Treating as simple noun."
      return noun trimmed
  else
    return noun trimmed


-- (将此代码段插入到您的 Statement 定义之后，prettyPrintContext 定义之前)

/--
为 Predicate 实现 ToString，使其可以在字符串插值中使用。
-/
instance : ToString Predicate where
  toString
    | .Be      => "be"
    | .Rewrite => "→"

/--
为 Statement 实现 ToString。
这是一个递归实现，它为语言的每种结构提供了清晰的文本表示。
这个表示对于人类调试和作为给 LLM 的输入都至关重要。
-/
partial instance : ToString Statement where
  toString s :=
    let rec go (s : Statement) : String :=
      match s with
      | .noun n => n
      | .formula subj pred obj => s!"({go subj}, {toString pred}, {go obj})"
      | .naming name body => s!"[{go name}, {go body}]"
      | .seq s1 s2 => s!"({go s1} • {go s2})"
    go s
/--
`prettyPrintContext` 函数将一个 `Context` 打印出来，
用 `<HOLE>` 来清晰地表示洞的位置。
这使得元层面的“问题”对用户可见。
-/
def prettyPrintContext (c : Context) : String :=
  let rec go (c : Context) : String :=
    match c with
    | .hole => "<HOLE>"
    | .formula_subj c' p o => s!"({go c'}, {p}, {o})"
    | .formula_obj s p c'  => s!"({s}, {p}, {go c'})"
    | .naming_name c' b    => s!"[{go c'}, {b}]"
    | .naming_body n c'    => s!"[{n}, {go c'}]"
    | .seq_left c' s2      => s!"({go c'} • {s2})"
    | .seq_right s1 c'     => s!"({s1} • {go c'})"
  go c

/--
`sessionLoop` 是交互的核心。
它代表了“元层面”的感知和提问循环。
-/
partial def sessionLoop (currentCenter : Statement) : IO Unit := do
  IO.println s!"\n-------------------------------------------------"
  IO.println s!"[Object Level] Current state of Gamma's center:"
  IO.println s!"  {currentCenter}"
  IO.println "-------------------------------------------------"

  -- 1. 元层面：识别问题。这里我们总是把问题定义为“接下来发生什么？”
  --    通过在当前语句的末尾创建一个洞来实现。
  let questionCtx : Context := .seq_right currentCenter .hole
  IO.println "[Meta Level] A question has been generated."
  IO.println s!"Context of the question: {prettyPrintContext questionCtx}"
  IO.println s!"Your answer will fill the <HOLE>."
  IO.println "Please provide a statement. Format: 'noun' or '(noun1 -> noun2)'"
  IO.print "> "

  -- 修复开始：正确获取标准输入流
  let stdin ← IO.getStdin
  let userInput ← stdin.getLine

  -- 退出条件
  if userInput.trim == "quit" then
    IO.println "Session ended."
    return

  -- ... 后续代码不变 ...


  -- 2. 元层面：接收并解析回答
  let userAnswer ← parseUserInput userInput

  -- 3. 交互之桥：填洞。从元层面下降到对象层面。
  IO.println s!"[Bridge] Filling the hole with your answer: {userAnswer}"
  let newCenter := questionCtx.fill userAnswer
  let worldToEvaluate : Statement := [noun Noun.gamma, newCenter]


  IO.println "\n[Object Level] New world state before evaluation:"
  IO.println s!"  {worldToEvaluate}"

  -- 4. 对象层面：执行归约。系统引擎开始工作。
  let finalWorld := eval worldToEvaluate
  IO.println "\n[Object Level] Final world state after evaluation:"
  IO.println s!"  {finalWorld}"

  -- 准备下一次循环
  match finalWorld with
  | .naming _ newCenterAfterEval => sessionLoop newCenterAfterEval
  | _ => IO.println "Error: World state is not in [Gamma, ...] form. Aborting."


/-- 主程序入口 -/
def main : IO Unit := do
  IO.println "Welcome to the Ternary Context Language Interactive Session."
  IO.println "This demonstrates the meta-object interaction loop."
  IO.println "We start with a simple statement 'start_token' in Gamma."

  let initialCenter : Statement := noun "start_token"
  sessionLoop initialCenter

end TCL.Interactive.Session

-- 如果你想直接在Lean中运行这个交互式会话，
-- 请取消下面这行代码的注释。
-- #eval TCL.Interactive.Session.main

-- (续写在 TCL.Interactive.Proof 和 TCL.Interactive.Session 之后)


-- ==================================================================
-- ## 扩展部分: 次协调逻辑与证明
-- ==================================================================
-- 本节实现了 TCL 的次协调特性，即通过“矛盾隔离”机制来处理“假”，
-- 并形式化证明了该机制可以有效防止逻辑爆炸。

namespace TCL.Paraconsistent
open TCL.Interactive

-- ### 1. “假”的定义与矛盾隔离引擎

-- 定义三种“假”作为特殊的原子名词
def Noun.false1 : Noun := "False1"
def Noun.false2 : Noun := "False2"
def Noun.false3 : Noun := "False3"

-- 便捷构造函数
def false1 : Statement := .noun Noun.false1
def false2 : Statement := .noun Noun.false2
def false3 : Statement := .noun Noun.false3

/-- 辅助函数，判断一个语句是否为我们定义的“假”之一 -/
def isFalse (s : Statement) : Bool :=
  match s with
  | .noun n => n == Noun.false1 || n == Noun.false2 || n == Noun.false3
  | _ => false

/--
在语句 `s` 中寻找第一个可归约表达式 (redex)。
此函数实现了“最左-最内”策略，并包含了矛盾隔离规则。
它是一个单一的、自递归的函数，保证了终止性。
-/
def findRedexParaconsistent (s : Statement) : Option Redex :=
  match s with
  -- 对于序列，它是唯一可能成为 redex 的结构
  | .seq s1 s2 =>
    -- 优先级 1: 在左子节点中寻找 redex (最左)
    (findRedexParaconsistent s1).map (fun r => { r with ctx := .seq_left r.ctx s2 }) <|>
    -- 优先级 2: 在右子节点中寻找 redex
    (findRedexParaconsistent s2).map (fun r => { r with ctx := .seq_right s1 r.ctx }) <|>
    -- 优先级 3: 如果子节点中没有，检查当前节点自身是否为 redex (最内)
    (match s2 with
     | .formula rewrite_subj .Rewrite rewrite_obj =>
       if s1 == rewrite_subj then
         if isFalse rewrite_obj then -- 矛盾隔离规则
           some ⟨.hole, s, .naming rewrite_obj rewrite_subj⟩
         else -- 标准重写规则
           some ⟨.hole, s, rewrite_obj⟩
       else none
     | _ => none)

  -- 对于其他结构，它们自身不能是 redex，所以只在其子节点中递归寻找
  | .naming n b =>
    (findRedexParaconsistent n).map (fun r => { r with ctx := .naming_name r.ctx b }) <|>
    (findRedexParaconsistent b).map (fun r => { r with ctx := .naming_body n r.ctx })

  | .formula subj pred obj =>
    (findRedexParaconsistent subj).map (fun r => { r with ctx := .formula_subj r.ctx pred obj }) <|>
    (findRedexParaconsistent obj).map (fun r => { r with ctx := .formula_obj subj pred r.ctx })

  -- 原子名词不是 redex，也没有子节点，是递归的终点
  | .noun _ => none

-- 使用新引擎的归约函数
def reduceStepParaconsistent (s : Statement) : Option Statement :=
  (findRedexParaconsistent s).map (fun r => r.ctx.fill r.replacement)

-- ### 2. 次协调一致性证明

namespace Proof
-- 形式化归约关系
inductive ReducesToP : Statement → Statement → Prop where
  | step {s s' : Statement} : reduceStepParaconsistent s = some s' → ReducesToP s s'
infix:80 " ⟶ₚ " => ReducesToP

inductive ReducesToPStar : Statement → Statement → Prop where
  | refl (s : Statement) : ReducesToPStar s s
  | step {s₁ s₂ s₃ : Statement} : (s₁ ⟶ₚ s₂) → ReducesToPStar s₂ s₃ → ReducesToPStar s₁ s₃
infix:80 " ⟶ₚ* " => ReducesToPStar

-- 核心不变量：收集语句中的原子名词集合
def nounsIn : Statement → Finset Noun
  | .noun n => {n}
  | .formula s _ o => nounsIn s ∪ nounsIn o
  | .naming n b => nounsIn n ∪ nounsIn b
  | .seq s1 s2 => nounsIn s1 ∪ nounsIn s2

def nounsInContext : Context → Finset Noun
  | .hole => ∅
  | .formula_subj c _ o => nounsInContext c ∪ nounsIn o
  | .formula_obj s _ c => nounsIn s ∪ nounsInContext c
  | .naming_name c b => nounsInContext c ∪ nounsIn b
  | .naming_body n c => nounsIn n ∪ nounsInContext c
  | .seq_left c s2 => nounsInContext c ∪ nounsIn s2
  | .seq_right s1 c => nounsIn s1 ∪ nounsInContext c

/--
此定理证明了 `findRedexParaconsistent` 的正确性：如果它找到了一个红式 `r`，
那么原始语句 `s` 确实可以被分解为 "包含红式的上下文" 填充 "红式本身"。
这是 `reduceStep` 正确性的基石。
-/
theorem find_decomposes (s : Statement) (r : Redex)
    (h_find : findRedexParaconsistent s = some r) :
    s = r.ctx.fill r.redex := by
  -- 对 `s` 进行归纳，其结构与 `findRedexParaconsistent` 的定义精确匹配。
  -- `generalizing r` 是必需的，因为在归纳的每一步中，r 的具体形式都可能改变。
  induction s generalizing r with
  | noun n =>
    simp [findRedexParaconsistent] at h_find

  | formula subj p obj ih_subj ih_obj =>
    -- 展开函数定义
    unfold findRedexParaconsistent at h_find
    -- 使用 match 模拟函数的执行流
    match h_subj_find : findRedexParaconsistent subj with
    | some r_subj =>
      -- 情况 1.1: 在主语中找到了 redex
      rw [h_subj_find] at h_find
      simp only [Option.map_some, Option.orElse_some] at h_find
      injection h_find with h_r_eq; subst h_r_eq
      rw [ih_subj r_subj h_subj_find]
      simp [Context.fill]
    | none =>
      -- 情况 1.2: 主语中没有 redex
      rw [h_subj_find] at h_find
      simp only [Option.map_none, Option.orElse_none] at h_find
      -- 关键修正：不使用 rw，而是直接应用 iff 引理的前向推理
      have h_exists := Option.map_eq_some_iff.mp h_find
      -- 使用 rcases 解构得到的存在量词
      rcases h_exists with ⟨r_obj, h_find_obj, h_r_eq⟩
      subst h_r_eq
      rw [ih_obj r_obj h_find_obj]
      simp [Context.fill]

  | naming name body ih_name ih_body =>
    -- 与 `formula` 的证明逻辑完全相同
    unfold findRedexParaconsistent at h_find
    match h_name_find : findRedexParaconsistent name with
    | some r_name =>
      rw [h_name_find] at h_find
      simp only [Option.map_some, Option.orElse_some] at h_find
      injection h_find with h_r_eq; subst h_r_eq
      rw [ih_name r_name h_name_find]
      simp [Context.fill]
    | none =>
      rw [h_name_find] at h_find
      simp only [Option.map_none, Option.orElse_none] at h_find
      -- 关键修正：同上
      have h_exists := Option.map_eq_some_iff.mp h_find
      rcases h_exists with ⟨r_body, h_find_body, h_r_eq⟩
      subst h_r_eq
      rw [ih_body r_body h_find_body]
      simp [Context.fill]

  | seq s1 s2 ih_s1 ih_s2 =>
    -- 展开函数定义
    unfold findRedexParaconsistent at h_find
    -- 模拟三层 <|> (即 orElse) 结构
    match h_s1_find : findRedexParaconsistent s1 with
    | some r_s1 =>
      -- 情况 2.1: 在 s1 中找到了 redex
      rw [h_s1_find] at h_find
      simp only [Option.map_some, Option.orElse_some] at h_find
      injection h_find with h_r_eq; subst h_r_eq
      rw [ih_s1 r_s1 h_s1_find]
      simp [Context.fill]
    | none =>
      -- 情况 2.2: 在 s1 中没有 redex
      rw [h_s1_find] at h_find
      simp only [Option.map_none, Option.orElse_none] at h_find
      -- 继续对 s2 进行分情况讨论
      match h_s2_find : findRedexParaconsistent s2 with
      | some r_s2 =>
        -- 情况 2.2.1: 在 s2 中找到了 redex
        rw [h_s2_find] at h_find
        simp only [Option.map_some, Option.orElse_some] at h_find
        injection h_find with h_r_eq; subst h_r_eq
        rw [ih_s2 r_s2 h_s2_find]
        simp [Context.fill]
      | none =>
        -- 情况 2.2.2: s1 和 s2 中都没有 redex
        rw [h_s2_find] at h_find
        simp only [Option.map_none, Option.orElse_none] at h_find
        -- h_find 现在是 `(match s2 with ...) = some r`
        -- 使用 split 战术来分解假设中的 match 表达式
        split at h_find
        · next h_s2_form => -- s2 匹配了 formula ...
          -- `h_s2_form` 是 s2 = rewrite_subj.formula ...
          -- `h_find` 自动被简化为 `(if ... then ... else ...) = some r`
          split_ifs at h_find
          · injection h_find with h_r_eq; subst h_r_eq; simp [Context.fill]
          · injection h_find with h_r_eq; subst h_r_eq; simp [Context.fill]
          · contradiction -- none = some r
        · next => contradiction -- s2 未匹配，结果是 none，与 h_find 矛盾


/--
**核心引理**: 如果 `findRedexParaconsistent` 成功地在语句 `s` 中找到了一个
红式 `r`，那么替换部分 `r.replacement` 的原子名词集合必然是红式本身
`r.redex` 的原子名词集合的子集。
-/

private theorem findRedexParaconsistent_on_seq_inner (s1 s2 : Statement)
    (h1 : findRedexParaconsistent s1 = none) (h2 : findRedexParaconsistent s2 = none) :
    findRedexParaconsistent (s1 • s2) =
      -- 核心修正：在 match 模式中直接匹配 .Rewrite，而不是在 if 中检查
      match s2 with
      | .formula s .Rewrite o => -- 直接匹配 .Rewrite
        if s1 == s then
          if isFalse o then some ⟨.hole, s1 • s2, .naming o s⟩
          else some ⟨.hole, s1 • s2, o⟩
        else none
      | _ => none := by
  -- 证明现在变得非常简单
  unfold findRedexParaconsistent
  rw [h1, h2]
  simp
  -- 对 s2 进行 cases 分解
  cases s2 with
  | formula s p o =>
    -- 对 p 进行 cases 分解
    cases p
    · -- case Be: simp 会自动处理所有分支
      simp
    · -- case Rewrite: simp 也会自动处理所有分支
      simp
  | _ => simp -- 其他构造器的情况很简单


theorem nouns_in_replacement_subset_of_redex_when_found (s : Statement) (r : Redex)
    (h_find : findRedexParaconsistent s = some r) :
    nounsIn r.replacement ⊆ nounsIn r.redex := by
  induction s generalizing r with
  | noun n =>
    simp [findRedexParaconsistent] at h_find

  | formula subj p obj ih_subj ih_obj =>
    unfold findRedexParaconsistent at h_find
    match h_subj_find : findRedexParaconsistent subj with
    | some r_subj =>
      rw [h_subj_find] at h_find; simp only [Option.map_some, Option.orElse_some] at h_find
      injection h_find with h_r_eq; subst h_r_eq
      exact ih_subj r_subj h_subj_find
    | none =>
      rw [h_subj_find] at h_find; simp only [Option.map_none, Option.orElse_none] at h_find
      have ⟨r_obj, h_obj_find, h_r_eq⟩ := Option.map_eq_some_iff.mp h_find
      subst h_r_eq; exact ih_obj r_obj h_obj_find

  | naming name body ih_name ih_body =>
    unfold findRedexParaconsistent at h_find
    match h_name_find : findRedexParaconsistent name with
    | some r_name =>
      rw [h_name_find] at h_find; simp only [Option.map_some, Option.orElse_some] at h_find
      injection h_find with h_r_eq; subst h_r_eq
      exact ih_name r_name h_name_find
    | none =>
      rw [h_name_find] at h_find; simp only [Option.map_none, Option.orElse_none] at h_find
      have ⟨r_body, h_body_find, h_r_eq⟩ := Option.map_eq_some_iff.mp h_find
      subst h_r_eq; exact ih_body r_body h_body_find

  | seq s1 s2 ih_s1 ih_s2 =>
    cases h_s1_find_eq : findRedexParaconsistent s1 with
    | some r_s1 =>
      unfold findRedexParaconsistent at h_find
      simp [h_s1_find_eq] at h_find
      subst h_find
      exact ih_s1 r_s1 h_s1_find_eq
    | none =>
      cases h_s2_find_eq : findRedexParaconsistent s2 with
      | some r_s2 =>
        unfold findRedexParaconsistent at h_find
        simp [h_s1_find_eq, h_s2_find_eq] at h_find
        subst h_find
        exact ih_s2 r_s2 h_s2_find_eq
      | none =>
        unfold findRedexParaconsistent at h_find
        simp [h_s1_find_eq, h_s2_find_eq] at h_find
        split at h_find
        · next rw_subj rw_obj =>
            split_ifs at h_find with h_eq_subj h_is_false
            · -- 子分支: redex 是 a → False
              injection h_find with h_r_eq; subst h_r_eq
              simp_all [nounsIn]
              rw [Finset.union_subset_iff]
              apply And.intro
              · -- 证明: nounsIn rw_obj ⊆ ...
                intro x hx
                -- 核心修正: 将集合并操作展开为逻辑或
                rw [Finset.mem_union, Finset.mem_union]
                apply Or.inr
                apply Or.inr
                exact hx
              · -- 证明: nounsIn rw_subj ⊆ ...
                intro x hx
                rw [Finset.mem_union, Finset.mem_union]
                apply Or.inr
                apply Or.inl
                exact hx

            · -- 子分支: redex 是 a → b
              injection h_find with h_r_eq; subst h_r_eq
              simp_all [nounsIn]
              intro x hx
              rw [Finset.mem_union, Finset.mem_union]
              apply Or.inr
              apply Or.inr
              exact hx

        · -- 分支 2: s2 没有匹配 (即 _)
          -- 在这个分支中, h_find 必然是 `none = some r`
          -- contradiction 战术会自动寻找这种矛盾
          contradiction


-- 引理1: `fill` 操作的集合性质
theorem nounsIn_fill (c : Context) (s : Statement) :
  nounsIn (c.fill s) = nounsInContext c ∪ nounsIn s := by
  induction c generalizing s <;>
  simp_all [nounsIn, nounsInContext, Context.fill, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]

theorem nouns_subset_of_step {s s' : Statement} (h : s ⟶ₚ s') :
  nounsIn s' ⊆ nounsIn s := by
  let ⟨h_eq⟩ := h
  have def_reduceStep : reduceStepParaconsistent s =
        (findRedexParaconsistent s).map (fun r => r.ctx.fill r.replacement) := rfl
  rw [def_reduceStep] at h_eq
  have ⟨r, h_find, h_s'_def⟩ : ∃ r, findRedexParaconsistent s = some r ∧ r.ctx.fill r.replacement = s' := by
    rw [Option.map_eq_some_iff] at h_eq
    exact h_eq
  have h_s_decomp : s = r.ctx.fill r.redex := find_decomposes s r h_find

  rw [←h_s'_def, h_s_decomp]
  rw [nounsIn_fill, nounsIn_fill]

  apply Finset.union_subset_union
  · apply Finset.Subset.refl
  · exact nouns_in_replacement_subset_of_redex_when_found s r h_find



-- 引理3: 多步归约保持名词集合的非扩张性
theorem nouns_subset_of_star {s s' : Statement} (h : s ⟶ₚ* s') :
  nounsIn s' ⊆ nounsIn s := by
  induction h with
  | refl => simp
  | step h_step _ ih => exact Finset.Subset.trans ih (nouns_subset_of_step h_step)

/-- 定义语句中子语句出现的递归关系 -/
inductive occursIn : Statement → Statement → Prop where
  | refl (s : Statement) : occursIn s s
  | formula_subj (s : Statement) (subj : Statement) (p : Predicate) (obj : Statement) :
      occursIn s subj → occursIn s (.formula subj p obj)
  | formula_obj (s : Statement) (subj : Statement) (p : Predicate) (obj : Statement) :
      occursIn s obj → occursIn s (.formula subj p obj)
  | naming_name (s : Statement) (name : Statement) (body : Statement) :
      occursIn s name → occursIn s (.naming name body)
  | naming_body (s : Statement) (name : Statement) (body : Statement) :
      occursIn s body → occursIn s (.naming name body)
  | seq_left (s : Statement) (s1 s2 : Statement) :
      occursIn s s1 → occursIn s (.seq s1 s2)
  | seq_right (s : Statement) (s1 s2 : Statement) :
      occursIn s s2 → occursIn s (.seq s1 s2)

/--
**主定理: 系统是次协调的**
一个包含矛盾的语句，无法归约为一个包含全新原子名词的任意语句。
-/
theorem no_explosion (s : Statement) (q : Noun)
    (h_init : q ∉ nounsIn s)
    : ∀ s', (s ⟶ₚ* s') → q ∉ nounsIn s' := by
  -- 引入归约路径和s'
  intro s' h_path
  -- 应用名词集合的非扩张性引理
  have h_subset := nouns_subset_of_star h_path
  -- 证明q不在s'中
  intro h_q_in_s'
  -- 根据集合包含关系，q必须在s中
  have : q ∈ nounsIn s := h_subset h_q_in_s'
  -- 但这与初始条件矛盾
  contradiction


end Proof
end TCL.Paraconsistent

#print axioms TCL.Paraconsistent.Proof.no_explosion
