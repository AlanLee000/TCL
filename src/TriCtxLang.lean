import Lean
/-!
# 三元组语境语言 (TCL) 的 Lean 4 实现

这个实现反映了原始设计的核心概念：
1.  **统一的数据结构**: `Statement` 通过 `noun`, `formula`, `naming`, `seq` 统一了原子、断言和两种结构化语境（嵌套与平展）。
2.  **语法糖**: `[a, b]` 和 `a • b` 让表达式更直观。
3.  **确定性归约引擎**: `reduce` 和 `reduceStep` 函数精确实现了“最左-最内” (Leftmost-Innermost) 的归约策略，确保了系统的合流性。
    - `reduceStep` 执行单步归约。
    - `reduce` 反复调用 `reduceStep` 直至范式。
4.  **全局求值上下文**: `eval` 函数将归约限制在 `[Gamma, ...]` 语境中，与原始设计完全一致。
-/

namespace TCL

-- ## 1. 核心类型定义
inductive Predicate where
  | Be
  | Rewrite
  -- | App -- 为未来模拟λ演算预留
  deriving Repr, BEq, Hashable, Inhabited

abbrev Noun := String

inductive Statement where
  | noun (n : Noun)
  | formula (subject : Statement) (pred : Predicate) (object : Statement)
  | naming (name : Statement) (body : Statement)
  | seq (s1 : Statement) (s2 : Statement)
  deriving Repr, BEq, Hashable, Inhabited

-- ## 2. 语法糖
notation:50 "[" a ", " b "]" => Statement.naming a b
infixr:65 " • " => Statement.seq

-- ## 3. 内置常量和辅助函数
def be      : Predicate := .Be
def rewrite : Predicate := .Rewrite

def Noun.gamma   : Noun := "Gamma"
def Noun.false1  : Noun := "False1"

def noun (n : Noun) : Statement := .noun n
def form (s : Statement) (p : Predicate) (o : Statement) : Statement := .formula s p o

-- ## 4. 归约引擎


/--
实现单步“最左-最内”归约策略。
该函数以深度优先的顺序遍历语句树：
1. 尝试归约左子节点。
2. 如果左子节点无法归约，尝试归约右子节点。
3. 如果所有子节点都已是范式，则尝试在当前节点应用重写规则。
-/
def reduceStep (s : Statement) : Option Statement :=
  match s with
  -- 对于序列，优先归约其成员
  | .seq s1 s2 =>
    -- 优先级 1: 尝试归约左侧部分
    if let some s1' := reduceStep s1 then
      some (s1' • s2)
    -- 优先级 2: 尝试归约右侧部分
    else if let some s2' := reduceStep s2 then
      some (s1 • s2')
    -- 优先级 3: 在当前节点应用核心重写规则 `a • (a → b) ↦ b`
    else match s2 with
         | .formula a .Rewrite b => if s1 == a then some b else none
         | _ => none
  -- 对于嵌套，优先归约其成员
  | .naming n b =>
    if let some n' := reduceStep n then
      some ([n', b])
    else if let some b' := reduceStep b then
      some ([n, b'])
    else
      none
  -- 对于三元组，优先归约其成员
  | .formula subj pred obj =>
    if let some subj' := reduceStep subj then
      some (form subj' pred obj)
    else if let some obj' := reduceStep obj then
      some (form subj pred obj')
    else
      none
  -- 原子名词是范式，无法归约
  | .noun _ => none

/--
`reduce` 函数，用于将一个语句完全归约到其范式。
它通过反复调用 `reduceStep` 来实现。
由于语言的表达能力可能导致无限循环（如图灵完备性），
我们将其标记为 `partial`。
-/
partial def reduce (s : Statement) : Statement :=
  match reduceStep s with
  | some s' => reduce s' -- 如果可以归约，则对新语句继续归约
  | none    => s       -- 如果无法归约，返回当前语句（已达范式）

/--
求值主函数。它只在全局语境 `Gamma` 中执行归约。
-/
def eval (world : Statement) : Statement :=
  match world with
  | .naming (.noun g_name) s =>
    if g_name == Noun.gamma then
      let s' := reduce s
      .naming (noun Noun.gamma) s'
    else
      world -- 如果不是 Gamma 语境，则不求值
  | _ => world -- 如果不是一个 naming 结构，则不求值

-- ## 5. 测试与演示

-- 定义一些原子用于测试
def a := noun "a"
def b := noun "b"
def c := noun "c"
def d := noun "d"
def ctx := noun "context"

-- 测试 1: 简单的直接归约
-- (a • (a → b)) 归约为 b
#eval reduce (a • (form a rewrite b))
-- 期望输出: TCL.Statement.noun "b"

-- 测试 2: 序列中的归约
-- (a • (a → b)) • c 归约为 b • c
#eval reduce ((a • (form a rewrite b)) • c)
-- 期望输出: TCL.Statement.seq (TCL.Statement.noun "b") (TCL.Statement.noun "c")

-- 测试 3: 嵌套归约 (最左-最内)
-- c • ( (a • (a → b)) • ( (a • (a → b)) → d ) )
-- 内层的 a•(a→b) 先归约为 b
-- 变成 c • ( b • (b → d) )
-- 再归约为 c • d
#eval reduce (c • ( (a • (form a rewrite b)) • (form (a • (form a rewrite b)) rewrite d) ))
-- 期望输出: TCL.Statement.seq (TCL.Statement.noun "c") (TCL.Statement.noun "d")

-- 测试 4: 在命名语境(naming)内的归约
-- [ctx, a • (a → b)] 归约为 [ctx, b]
#eval reduce ([ctx, a • (form a rewrite b)])
-- 期望输出: TCL.Statement.naming (TCL.Statement.noun "context") (TCL.Statement.noun "b")

-- 测试 5: 无法归约的项
-- a • (c → b) 因为主语不匹配，无法归约
#eval reduce (a • (form c rewrite b))
-- 期望输出: TCL.Statement.seq (TCL.Statement.noun "a") (TCL.Statement.formula (TCL.Statement.noun "c") TCL.Predicate.Rewrite (TCL.Statement.noun "b"))


end TCL

-- ==================================================================
-- ## 6. 附录：合流性 (Confluence) 的形式化证明
-- ==================================================================
namespace TCL.Proof
open TCL

-- ### 6.1 形式化定义

-- 定义一步归约关系 `s ⟶ s'`
inductive ReducesTo : Statement → Statement → Prop where
  | step {s s' : Statement} : reduceStep s = some s' → ReducesTo s s'

-- 为一步归约关系定义中缀表示法
infix:80 " ⟶ " => ReducesTo

/--
定义多步归约关系 `s ⟶* s'`。
这是 `⟶` 的自反传递闭包，我们在这里将其显式地定义出来，
以便于进行归纳证明。
-/
inductive ReducesToStar : Statement → Statement → Prop where
  | refl (s : Statement) : ReducesToStar s s
  | step {s₁ s₂ s₃ : Statement} : (s₁ ⟶ s₂) → ReducesToStar s₂ s₃ → ReducesToStar s₁ s₃

-- 为多步归约关系定义中缀表示法
infix:80 " ⟶* " => ReducesToStar

-- ### 6.2 核心引理与主定理

/--
**引理 1：归约的确定性 (Determinism)**
-/
theorem reduction_is_deterministic (s s₁ s₂ : Statement) :
  (s ⟶ s₁) → (s ⟶ s₂) → s₁ = s₂ := by
  -- FIX: 使用正确的 rintro 模式
  rintro ⟨heq₁⟩ ⟨heq₂⟩
  -- heq₁ : reduceStep s = some s₁
  -- heq₂ : reduceStep s = some s₂
  rw [heq₁] at heq₂
  injection heq₂ with h_eq
  done

/--
**辅助引理：多步归约的传递性 (Transitivity)**
-/
theorem transitivity (s₁ s₂ s₃ : Statement) : (s₁ ⟶* s₂) → (s₂ ⟶* s₃) → (s₁ ⟶* s₃) := by
  -- 首先，只引入我们想对其进行归纳的第一个假设 h_path₁
  intro h_path₁

  -- 对 h_path₁ 进行归纳, 并泛化 s₃。
  -- 我们不使用 `with` 关键字，而是让 induction 创建两个证明目标 (goals)，
  -- 每个目标对应一个构造器。
  induction h_path₁ generalizing s₃

  -- 第一个目标: 处理 'refl' 的情况
  case refl =>
    -- Lean 自动处理了 s₁ = s₂ 的替换。
    -- 目标是: (s₁ ⟶* s₃) → (s₁ ⟶* s₃)
    intro h_path₂
    exact h_path₂

  -- 第二个目标: 处理 'step' 的情况
  -- 使用 `case` 战术，并为所有由 induction 引入的变量和归纳假设提供名字。
  case step s_mid h_step h_path_rest ih =>
    -- Lean 在这里成功地引入了所有部分:
    -- s_mid:       Statement          -- 中间点
    -- h_step:      s₁ ⟶ s_mid         -- 第一步的证明
    -- h_path_rest: s_mid ⟶* s₂        -- 剩余路径的证明
    -- ih:          ∀ (s₃), (s₂ ⟶* s₃) → (s_mid ⟶* s₃) -- ！！！这就是我们需要的归纳假设！！！

    -- 我们的目标是: (s₂ ⟶* s₃) → (s₁ ⟶* s₃)
    intro h_path₂ -- 引入 h_path₂ : s₂ ⟶* s₃

    -- 现在的目标是 s₁ ⟶* s₃

    -- 构造 s₁ ⟶* s₃ 的证明:
    -- 1. 构造第一步
    apply ReducesToStar.step
    --  1a. 提供第一步的证明 `h_step`
    exact h_step
    --  1b. 提供剩余路径 `s_mid ⟶* s₃` 的证明
    --      我们可以通过应用归纳假设 `ih` 来得到它
    exact ih s₃ h_path₂
  done
/--
**引理 2：钻石引理 (Strip Lemma)**
如果 m 能一步归约到 m₁，且 m 能多步归约到 m₂，
那么一定存在一个共同的汇合点 m₃。
对于确定性系统，此引理的证明较为直接。
-/
theorem strip_lemma (m m₁ m₂ : Statement) :
  (m ⟶ m₁) → (m ⟶* m₂) → ∃ m₃, (m₁ ⟶* m₃) ∧ (m₂ ⟶* m₃) := by
  -- 引入两个前提假设
  intro h_m_m₁ h_path_m_m₂

  -- 对多步归约路径 `h_path_m_m₂` 进行归纳。
  -- 我们不使用 `with`，而是让 induction 创建 goals，然后用 `case` 逐个处理。
  induction h_path_m_m₂

  -- `induction` 创建了两个 goal，一个对应 `refl`，一个对应 `step`。

  -- Goal 1: 处理 `refl` 的情况
  case refl m =>
    -- 在此分支, `induction` 策略已经自动推断出 `m = m₂` 并完成了替换。
    -- 我们的目标是: ∃ m₃, (m₁ ⟶* m₃) ∧ (m ⟶* m₃)
    -- 我们选择 m₃ := m₁
    exists m₁
    -- 现在需要证明 (m₁ ⟶* m₁) ∧ (m ⟶* m₁)
    apply And.intro
    -- 1. 证明 m₁ ⟶* m₁，这通过自反性直接成立
    . exact ReducesToStar.refl m₁
    -- 2. 证明 m ⟶* m₁，我们已知 `h_m_m₁ : m ⟶ m₁`，
    --    将其提升为多步归约即可。
    . exact ReducesToStar.step h_m_m₁ (ReducesToStar.refl m₁)

  -- Goal 2: 处理 `step` 的情况
  -- 使用 `case` 并为所有变量提供清晰的命名
  case step m m_mid m₂_rest h_m_mmid h_path_mmid_m₂_rest ih =>
    -- 这里 `induction` 分解出了:
    -- m, m_mid, m₂_rest : Statement    (路径上的项，注意 m₂ 在这里是 m₂_rest)
    -- h_m_mmid          : m ⟶ m_mid    (第一步归约的证明)
    -- h_path_mmid_m₂_rest : m_mid ⟶* m₂_rest (剩余路径的证明)
    -- ih                : ...          (归纳假设，这里我们甚至用不到它)
    -- 我们还有来自外部的 `h_m_m₁ : m ⟶ m₁`

    -- 关键步骤：我们有两条从 `m` 出发的一步归约:
    -- 1. h_m_m₁   : m ⟶ m₁
    -- 2. h_m_mmid : m ⟶ m_mid
    -- 由于系统是确定性的，`m₁` 和 `m_mid` 必须是同一个项。
    have h_eq : m₁ = m_mid := reduction_is_deterministic m m₁ m_mid h_m_m₁ h_m_mmid

    -- 使用 `subst` 将 `m_mid` 替换为 `m₁`，这会清理上下文并更新相关假设。
    subst h_eq

    -- 替换后, `h_path_mmid_m₂_rest` 的类型变为 `m₁ ⟶* m₂_rest`。
    -- 我们的目标是: ∃ m₃, (m₁ ⟶* m₃) ∧ (m₂_rest ⟶* m₃)
    -- 这个目标现在非常直接，我们选择 m₃ := m₂_rest。
    exists m₂_rest

    -- 现在需要证明 (m₁ ⟶* m₂_rest) ∧ (m₂_rest ⟶* m₂_rest)
    apply And.intro
    -- 1. 证明 m₁ ⟶* m₂_rest，这正是我们更新后的假设 `h_path_mmid_m₂_rest`
    . exact h_path_mmid_m₂_rest
    -- 2. 证明 m₂_rest ⟶* m₂_rest，这通过自反性直接成立
    . exact ReducesToStar.refl m₂_rest
  done

theorem confluence (m m₁ m₂ : Statement) :
  (m ⟶* m₁) → (m ⟶* m₂) → ∃ m₃, (m₁ ⟶* m₃) ∧ (m₂ ⟶* m₃) := by
  intro h_path₁
  induction h_path₁ generalizing m₂ with
  | refl =>
    intro h_path₂
    exists m₂
    exact ⟨h_path₂, .refl _⟩

  | @step m mid _ h_step h_rest ih =>  -- 注意：我们显式指定了起点m和中间点mid
    intro h_path₂
    have ⟨m₂', h_mid_to_m₂', h_m₂_to_m₂'⟩ := strip_lemma m mid m₂ h_step h_path₂
    have ⟨m₃, h_m₁_to_m₃, h_m₂'_to_m₃⟩ := ih m₂' h_mid_to_m₂'
    have h_m₂_to_m₃ := transitivity m₂ m₂' m₃ h_m₂_to_m₂' h_m₂'_to_m₃
    exists m₃
    done



end TCL.Proof


-- 检查证明是否使用了不希望的公理（如选择公理）
-- 预期输出为空，表示证明是构造性的。
#print axioms TCL.Proof.confluence
