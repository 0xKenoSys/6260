+++
title = "6260 notes: lemma辅助终止,decreases,length_drop,chunks"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "chunks", "take", "drop", "length_drop", "decreases"]
toc = true
+++

## chunks-terminates.dfy

**背景:Dafny 为什么管终止?** 每个递归函数都必须让 Dafny 相信它不会无限递归下去。多数情况这是免费的:只要递归调用作用在 match 拆出来的**子结构**上(比如对 Cons(h,t) 递归调用 t),参数在结构上严格变小,Dafny 自动认可——这叫**结构递归**。

这个文件的主角 chunks 恰好**不是**结构递归,所以要动手。

## take 与 drop：结构递归,免费

take(n, l) 取列表前 n 个元素;drop(n, l) 扔掉前 n 个,留下剩余部分。两者的递归调用都作用在 l 拆出的尾巴 t 上,**免费通过**。

```dafny
include "../core-list.dfy"

function take<T>(n:nat, l:list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(h,t) => if n == 0 then Nil else Cons(h,take(n-1, t))
}

function drop<T>(n:nat, l:list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(h,t) => if n == 0 then l else drop(n-1,t)
}
```

## length_drop：此刻看似闲置

一条早前证过的 lemma,读作:对任意 n、l,**drop 掉 n 个之后的长度 == 若 n ≥ 原长则 0,否则原长 - n**。空 `{}` 即通过(Dafny 的自动归纳搞得定)。它此刻看似闲置——往下看。

```dafny
lemma length_drop<T>(n:nat, l:list<T>)
  ensures length(drop(n,l)) == if n >= length(l) then 0 else length(l) - n {}
```

## 问题所在：drop(n,l) 不是子结构

chunks(n, l) 把 l 切成每块 n 个元素的小列表组成的列表,例如 chunks(2, [1,2,3,4,5]) == [[1,2],[3,4],[5]]。

**递归调用是 chunks(n, drop(n,l))。drop(n,l) 不是 match 从 l 上拆下来的子结构——它是另一个函数算出来的结果。** Dafny 不会为了查终止而去展开 drop 的定义,所以在它眼里 drop(n,l) 和 l **毫无大小关系**。原文件报错:

```
Error: cannot prove termination; try supplying a decreases clause
```

## 修复分两步，各解决一半问题

**第一步:`decreases length(l)`——告诉 Dafny 该用什么尺子。** 不是列表的结构,而是它的长度这个数。(decreases 是贴在递归门口的模具,每次进门都量一次,量出来的数必须严格递减且不能低于 0。)于是终止义务变成一道具体的数学题:**证明 length(drop(n,l)) < length(l)**。

**第二步:调用 length_drop(n, l)。** 光有尺子还不够——那道数学题 Dafny 依然做不出来,理由同上:它不展开 drop。但手里正好有一条现成的定理说清了 length(drop(n,l)) 是多少。**在递归调用之前调用这条 lemma,就是把该定理实例化到当前的 n 和 l 上,让这个事实进入求解器的视野。** 之后它就能推了:l 非空 ⟹ length(l) ≥ 1,又 n ≥ 1,两种情况 length(drop) 要么是 0 要么是 length(l)-n,都严格小于 length(l)。

**语法上的新事物**:函数体是表达式的世界,本来容不下语句——**lemma 调用是唯一的例外**,写成「lemma调用; 表达式」:lemma 不计算、无副作用,它只是往求解器的视野里放一条知识,不破坏「函数体 = 表达式」的纯洁性。

**requires 0 < n 是终止的命根子**:若允许 n == 0,drop(0,l) == l,长度不减,函数真的会死循环。

```dafny
function chunks<T>(n:nat, l:list<T>) : list<list<T>>
  requires 0 < n
  decreases length(l)              // 修复①：指定尺子
{
    match l
    case Nil => Nil
    case _ =>
        length_drop(n, l);         // 修复②：递归门口先亮出定理
        Cons(take(n,l),chunks(n,drop(n,l)))
}
```
