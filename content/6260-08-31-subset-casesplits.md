+++
title = "case split,账目表,展开一次一层,subset_widen"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "lset", "subset", "subset_member", "subset_trans", "subset_widen", "subset_refl"]
toc = true
+++

## subset-casesplits.dfy（Lecture 09）：证明里的分情况讨论

**这一课的核心思想,一段话讲完**:函数经常"看情况办事"——列表空不空?某条件真不真?函数分岔了,关于它的证明多半也得跟着分岔——**证明的结构模仿函数的结构**。

在证明体(语句的世界)里,分岔有两件工具:**match 按数据形状分,if 按真假分**。它们的工作原理(讲师的**"事实云"**比喻):每个分支各自向求解器的视野注入"若走到我这支,则……"的事实。if 分支给出 P ⟹ φ,else 分支给出 ¬P ⟹ φ;两支都证出同一个 φ,P 真假已无所谓,φ 成立。match 同理:Nil 证一遍、Cons 证一遍,而列表**非 Nil 即 Cons,无路可逃,结论封顶**。

注意语法差异:函数体里写 `if c then x else y`(表达式);证明体里写 `if c { } else { }`(语句,带花括号)。**又是三分类。**

**原始文件的状态**:subset_trans 和 subset_refl 是**无体 lemma**——连花括号都没有,Dafny 视之为**"赊账的公理"**并给警告(Problems 面板里那条 "Add the {:axiom} attribute..." 就是它)。作业就是把账还上:补出证明体。本文件补全后在 Dafny 4.11.0 下验证通过:**6 verified, 0 errors**。

## member 与 subset

member:老朋友,a 在 A 里吗?subset:A 的每个元素都在 B 里吗?沿 A 递归逐个检查。

```dafny
include "../core-list.dfy"

predicate member(a : int, A : lset)
{
    match A
    case Nil => false
    case Cons(x,xs) => a == x || member(a,xs)
}

predicate subset(A : lset, B : lset)
{
    match A
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}
```

## subset_member：下面那条定理的原料

读作:**若 x ∈ A 且 A ⊆ B,则 x ∈ B。** 空体即过:自动归纳沿 A 走通了。

语法小注:**两个 requires 并排写,等价于用 && 连成一个**——多条前提逐行列,是 Dafny 的惯用排版。

```dafny
lemma subset_member(x:int, A:lset, B:lset)
  requires member(x,A) requires subset(A,B)
  ensures member(x,B) {}
```

## subset_trans：账目表

传递性。空体不行(实测报错),按讲义提示列一张**"手里有什么 vs 想要什么"**的账目表。对 A 做 match,看 Cons(x,xs) 支:

**想要**:subset(Cons(x,xs), C),展开成两块——① member(x, C);② subset(xs, C)。
**手里**:requires 展开后有 member(x,B)、subset(xs,B)、subset(B,C)。

**补②**:递归调用 subset_trans(xs, B, C)——即归纳假设,它的前提 subset(xs,B) 和 subset(B,C) 手里都有。**补①**:"x ∈ B 且 B ⊆ C ⟹ x ∈ C"——这正是 subset_member 的形状,实例化 subset_member(x, B, C)。账平了,Nil 支空真,留空。

```dafny
/* A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C */
/* build what-do-we-have vs what-do-want table */
lemma subset_trans(A : lset, B : lset, C : lset)
  requires subset(A,B)
  requires subset(B,C)
  ensures subset(A,C)
{
    match A
    case Nil =>
    case Cons(x,xs) =>
        subset_member(x, B, C);
        subset_trans(xs, B, C);
}
```

## 展开的纪律：一次一层

展开不是灵感,是一套机械操作。规则只有一条:**一个 predicate 调用,只有当它第一个 match 的那个参数的构造器已知时,才允许展开,且一次只展开一层。**

`subset(A,C)` 里 A 形状未知——展不动。这就是为什么 `match A` 必须先行:**case split 的唯一目的,就是把构造器喂给定义,让展开合法**。脑子痒的地方在这里:想直接展开,但展开的前置条件是"知道形状",顺序反了。

纸上的账本,`Cons(x,xs)` 分支,三步:

**第一步,抄下双方,不展开。**

```
有: subset(Cons(x,xs), B)     要: subset(Cons(x,xs), C)
有: subset(B, C)
```

**第二步,凡是构造器已知的,各展开一层,然后立刻停。** subset 的定义 Cons 分支是 `member(x,B) && subset(xs,B)`,所以:

```
有: member(x,B)               要: member(x,C)
有: subset(xs,B)              要: subset(xs,C)
有: subset(B,C)   ← B 形状未知，原样留着
```

注意 `subset(B,C)` 不许碰——B 是变量,不知道是 Nil 还是 Cons。**留着的这条不是废料,它是桥。**

**第三步,逐行配账:每一条"要",问它能不能由若干条"有"通过一个已知 lemma 或递归得到。**

```
要 member(x,C):  有 member(x,B) + subset(B,C)  → subset_member(x,B,C)
要 subset(xs,C): 有 subset(xs,B) + subset(B,C) → subset_trans(xs,B,C)（递归，xs 结构变小）
```

**写出来的 lemma body 就是第三步的右栏,一行一条。** Nil 分支在第二步就结清了——"要"展开成 true,无账可配,留空。

停在一层是纪律,不是保守。展开到底会把账本淹掉,而 Dafny 自己也只按需展开一层。展开范围就是:**match 给一层,定义吃一层,配一次账。循环即证明。**

## subset_widen：归纳假设太窄时,搭桥

先看它**为什么必须存在**。直接归纳证 subset_refl 会撞墙,账目表把墙照得清清楚楚:

**想要**:subset(Cons(x,xs), Cons(x,xs)),展开——① member(x, Cons(x,xs)),头就在头上,白送;② subset(xs, Cons(x,xs)),**缺口在此**。
**手里**:归纳假设 subset_refl(xs) 只给 subset(xs, xs)。

对不上:手里的右边是 xs,想要的右边是 Cons(x,xs)——**归纳假设的 B 太窄**。这是归纳证明里的经典困局:**定理本身没错,但它的原样归纳假设不够用,得另立一条更合用的定理来搭桥。** 桥就是"加宽":子集关系不怕右边多塞一个元素。

```dafny
lemma subset_widen(A : lset, y : int, B : lset)
  requires subset(A,B)
  ensures subset(A, Cons(y,B))
{
    match A
    case Nil =>
    case Cons(x,xs) => subset_widen(xs, y, B);
    // Cons 支的账：想要 member(x,Cons(y,B))——手里有 member(x,B)，
    // 塞进更大的表当然还在，求解器自己看穿；想要 subset(xs,Cons(y,B))
    // ——归纳假设直接给。留一行递归调用即可。
}
```

## subset_refl：过桥,两步走完

自反性。有了桥,两步:归纳假设 subset_refl(xs) → 手里有 subset(xs, xs);过桥 subset_widen(xs, x, xs) → 变出 subset(xs, Cons(x,xs)),正是缺口②。

```dafny
/* A ⊆ A */
lemma subset_refl(A : lset)
  ensures subset(A,A)
{
    match A
    case Nil =>
    case Cons(x,xs) =>
        subset_refl(xs);
        subset_widen(xs, x, xs);
}
```
