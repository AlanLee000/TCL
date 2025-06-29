# 三元组语境语言 (Triple Contextual Language - TCL)

[![License: MIT](https://img.shields.io/badge/Code%20License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: CC BY 4.0](https://img.shields.io/badge/Docs%20License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

一个旨在统一**知识表示**、**逻辑推理**和**通用计算**的形式化语言。本项目包含其完整的理论论述和在 Lean 4 中经过形式化验证的参考实现。
完整理论论述见[TriCtxLang](./docs/TriCtxLang.md)
一个更可读的哲学动机分析见[TCL_drive](./docs/TCL_drive.md)

---

## 目录
- [三元组语境语言 (Triple Contextual Language - TCL)](#三元组语境语言-triple-contextual-language---tcl)
  - [目录](#目录)
  - [核心思想](#核心思想)
  - [语言定义](#语言定义)
    - [语法结构](#语法结构)
    - [两种语境操作](#两种语境操作)
    - [语义核心：三元组](#语义核心三元组)
  - [关键特性](#关键特性)
    - [语法-语义分裂](#语法-语义分裂)
    - [元-对象交互：作为提问的“洞”](#元-对象交互作为提问的洞)
    - [图灵完备性](#图灵完备性)
    - [合流性 (Confluence)](#合流性-confluence)
    - [次协调性：矛盾隔离](#次协调性矛盾隔离)
  - [Lean 4 实现](#lean-4-实现)
    - [文件结构](#文件结构)
  - [如何构建与验证](#如何构建与验证)
  - [许可协议](#许可协议)
  - [AI声明](#ai声明)
  - [如何引用](#如何引用)

## 核心思想

TCL 的出发点是将知识库的结构（如文件树）与知识库的内容（如语句）统一起来。它发展了Lisp **代码即数据** 的思想，体现为 **语境、语句、语词的统一**。

TCL 这样理解元：**元即感知**。也就是说: **元语言是包含空缺（洞）的对象语言，而一个空缺就是一个提问。** 因此，TCL 是一个问答逻辑系统。

TCL 这样理解同一性：同一性的实质是分裂的，是由 **等价关系** 和 **重写** 构成的复合概念。 揭示了“一个事物是什么”（语义）和“一个事物在哪里”（语法/结构）之间的根本区别，即 **语法-语义分裂**。

TCL 实现了知识库的 **三元组表示RDF** 和 **JSON数据格式** 的结合，并把重写实现为一种三元组形式的操作，因此是一个 **动态的知识库** 。

## 语言定义

### 语法结构

整个语言由一种统一的递归类型 `<statement>` 构成：

```
<noun>      ::= a | b | c | ...
<predicate> ::= be | → | ...
<formula>   ::= (<statement>, <predicate>, <statement>)
<statement> ::= <noun>
            | <formula>
            | [<statement>, <statement>]  // 语境深入 (Naming/Scoping)
            | <statement> . <statement>   // 语境平展 (Sequencing)
```

### 两种语境操作

1.  **语境深入 `[a, b]`**: 一个非交换、非结合的**定位**操作。它声明 `b` 存在于 `a` 所命名的视角或空间下，构建了系统的层次结构（树）。
2.  **语境平展 `a . b`**: 一个非交换、结合的**排序**操作。它定义了 `a` 和 `b` 之间的先后顺序，构建了树中同一层级的序列。

这两种操作共同定义了一个**有序的地址树**，其中每个 `statement` 都拥有一个唯一的结构化位置。

### 语义核心：三元组

三元组 `(S, P, O)` 是**断言和计算**的核心。

-   `(S, be, O)`: 声明一种静态的、逻辑上的**等价关系**。
-   `(S, →, O)`: 定义一条动态的、操作上的**重写指令**。

系统的计算引擎由一条全局重写规则驱动，该规则将 `→` 指令应用于其左侧的语境：
`([Gamma, <[context, S]> . (S, →, O)], →, [Gamma, <[context, O]>)`

## 关键特性

### 语法-语义分裂

TCL 展示了语法身份（位置）和语义身份（行为）的分裂。

-   `v_a := [ctx, a]` 和 `v_b := [ctx, b]` 在语法上是**不同**的，因为它们的中心内容不同。
-   但如果我们在语境中加入一条重写规则 `(a, →, b)`，那么 `v_a` 在计算行为上将等同于 `v_b`。

系统通过 `→` 谓词，在结构上不同的实体之间建立了可计算的语义联系。

### 元-对象交互：作为提问的“洞”

这是 TCL 核心的概念。

-   **提问**: 一个不完整的结构，如 `[<[context,]>, statement]`，就是一个元语言层面的**问题**：“什么东西命名了 `statement`？”
-   **回答**: 将一个具体的 `statement` **填入**这个洞中，就是对问题的回答，使元语言问题“坍缩”为对象语言陈述。

这个过程形成了一个元-对象层面的语义循环，描述了一个通过“提问-回答”来学习和演化的系统。开发者认为，这结合了当前 LLM 的本质功能：**作为感知层和填洞者**。

### 图灵完备性

TCL 被证明是图灵完备的。这通过模拟无类型 λ-演算的 β-归约实现。

-   `λx.M` 编码为 `[M, x]`。
-   应用 `(λx.M) N` 被一条公理重写为 `M . (x, →, N)`，复用了系统原生的重写引擎来完成替换。

### 合流性 (Confluence)

TCL 的归约系统是**合流的**。这源于其**确定性的归约策略**（最左-最内）。此属性已在 `TCL.Proof.confluence` 中使用 Lean 4 **形式化证明**。这意味着任何给定的语句，无论以何种顺序归约其可归约部分，最终都会达到唯一的范式（如果它终止的话）。

### 次协调性：矛盾隔离

TCL 是一个**次协调** (Paraconsistent) 系统。它通过**矛盾隔离**机制避免了逻辑爆炸（即从一个矛盾可以推出任何结论）。

-   当系统遇到一个矛盾，如 `a . (a, →, False)` 时，它不会崩溃。
-   相反，它会将导致矛盾的语句 `a` **封装**到一个以谬误 `False` 命名的子语境中：`[False, a]`。
-   这个矛盾被有效“标记”和“隔离”，而不会污染外部语境。

## Lean 4 实现

本项目提供了一个基于理论的 Lean 4 实现。

### 文件结构
-   `TriCtxLang.lean`: 定义了 TCL 的核心数据结构 (`Statement`, `Predicate`) 和确定性的归约引擎 (`reduceStep`, `reduce`, `eval`)。 包含了对系统**合流性**的形式化证明。
-   `TCL1.lean`: 定义了TCL的包含元层的实现，并重新实现了TCL的核心数据结构，包含了对系统合流性的形式化证明、假的实现与次协调一致性的证明。
-   `Multihole.lean`：定义了多洞感知机制的元处理层。
-   `Main.lean`：实现了多洞感知机制的元处理层（Multihole.lean）和计算层（TCL1）的交互。

## 如何构建与验证

您需要安装 [Lean 4](https://lean-lang.org)和Mathlib。

## 许可协议

本项目采用混合许可模式：

-   所有 **Lean 源代码** (`*.lean` 文件) 均根据 [**MIT 许可证**](LICENSE) 授权。
-   所有**其他内容**，包括本文档和理论论述，均根据 [**Creative Commons Attribution 4.0 International (CC BY 4.0)**](LICENSE-CC-BY-4.0.md) 授权。

## AI声明

部分代码和文本由LLM生成，作者进行了整理但不完备，因此某些文本和注释可能有AI痕迹。

## 如何引用

如果您在您的研究中使用了本项目的思想或代码，请引用本 GitHub 仓库。

```bibtex
@misc{TCL_github,
  author = {[Your Name or Alias]},
  title = {Ternary Contextual Language: A Formalism for Unifying Knowledge, Logic, and Computation},
  year = {2023},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/AlanLee000/TCL}},
}
```