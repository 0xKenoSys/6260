+++
title = "f6260 notes: orall,trigger,witness,forall,subset_forall"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "forall", "exists", "trigger", "divides", "primeCheck", "subset_forall", "reverse_subset"]
toc = true
+++

## simplest-quantifiers.dfy：forall 语法,一次记全

**一段话说清这一课在干什么**:到目前为止,其实一直在证"对任意……"的定理而不自知——每条 lemma 的参数表就是隐含的 forall 清单(早先那句**「lemma 参数 = for all 清单」在这一课被扶正为官方理论**)。顶层的 forall 可以省略不写,所以一直相安无事。这一课解决的新问题是:**当 forall 不在顶层、而要出现在公式内部时**(requires 里、ensures 里、assert 里),就必须写出真正的 forall 语法。

**语法一次记全**:`forall 变量 : 类型 | 前置条件 :: 公式`。竖线和前置条件可选;:: 后面是主体公式。两种等价写法:

```dafny
forall n : nat | 0 < n :: foo(n)        // 竖线式
forall n : nat :: 0 < n ==> foo(n)      // 蕴含式
```

**铁律(讲师反复强调的 99% 规则):forall 配蕴含 ==>,exists 配合取 &&。** 若发现自己写了 exists 配 ==>,几乎必然写错了。

**新事物①:无体谓词。** foo 只有签名没有身体——它是一个**未解释谓词**:Dafny 对 foo(0)、foo(1)…的真假一无所知,只当它是"某个任意的性质"。这让下面的 lemma 一举谈论**一切可能的性质**:无论 foo 是什么,只要满足两条前提,结论就成立。抽象的力量。

逐行读这条定理:前提一,对一切比 0 大的 n,foo(n) 成立(覆盖 1,2,3,…);前提二,foo(0) 也成立(把 0 单独补上);结论,对一切自然数 n,foo(n) 成立。逻辑上就是**"0 的情形 + 非 0 的情形 = 全部情形"**,一个最朴素的分情况拼图。Dafny 空手即证——体内那行 assert 其实可有可无(求解器早已自行得出),讲义留着它是为了展示:**forall 公式和普通公式一样,可以被 assert、被 requires、被 ensures——它就是个公式**。

```dafny
predicate foo(n:nat)

lemma dumb()
  requires forall n : nat :: 0 < n ==> foo(n)
  requires foo(0)
  ensures forall n : nat :: foo(n)
{
  assert forall n : nat :: foo(n);
}
```

**新事物②:棕色波浪线 = 触发器警告。** 打开本文件会看到 Dafny 抱怨 "Could not find a trigger for this quantifier"。**触发器(trigger)是求解器处理量词的内部机关**:它需要公式里有一个函数应用样式的**"把手"**(如 foo(n)),才知道何时把 forall 实例化到具体的值上。这里 foo(n) 恰好就是把手,所以虽有警告,验证照过。警告的意思是"我勉强找到了/找不到稳定把手,**证明可能脆弱**"——记住这个概念,下一个文件里它将从警告升级为死刑。

## smallestExists.dfy：一个故意设计的失败

先把结论钉死:**这条 lemma 照原样证不出来,而且这正是它存在的目的。** 讲义第一行注释 "look at the brown!" 说的就是满屏棕色触发器警告——这文件是拿来看警告、理解失败的,不是拿来做的。讲师课上的原话(转录):"这超出了 Dafny 能优雅处理的范围……我想我能证出来,但我不确定我想试。"

定理本身读作:**存在一个自然数 s,使得对一切自然数 m 都有 s ≤ m**——即"存在最小的自然数"。数学上显然为真,证人(witness)就是 0:0 ≤ 一切自然数。

```dafny
lemma smallestExists()
  ensures exists s : nat :: forall m : nat :: s <= m
{
  // 空体失败。以下"显然该有用"的救援在 Dafny 4.11.0 下逐一实测，全部无效：
  //
  // assert forall m : nat :: 0 <= m;          // 喂证人事实 ✗
  // var s0 : nat := 0;
  // assert forall m : nat :: s0 <= m;         // 具名证人 ✗
  // （借辅助引理喂、用命名谓词包一层、
  //   甚至上 {:trigger} 哑函数手术——全部 ✗）
}
```

**为什么救不活?症结在触发器。** 求解器摆弄量词,靠的是公式里的函数应用充当"把手"。可 `s <= m` 这个公式体里**一个函数应用都没有**——只有裸变量和 ≤。无把手,则求解器面对 exists 不知该拿哪个值试,面对内层 forall 不知何时实例化;再叠上 **exists 套 forall 的双层嵌套结构**,机器彻底罢工。把证人 0 递到它嘴边,它也咬不住——因为"咬"这个动作本身需要把手。

**该带走的教训**:

1. **Dafny 的强项是证程序性质,不是做形式数学**;嵌套量词是它能力边界的悬崖,数学家日常写的 ∃s∀m 在这里是禁区。
2. **棕色警告是预兆**:看到 "could not find a trigger",就该预期证明可能脆弱乃至不可得。
3. **定理为真 ≠ 工具可证。** 二者的落差,正是这门课后半段所有"绕路技巧"(辅助引理、改述、加把手)存在的理由。

下一个文件会展示同样带量词的定理如何因为体内有 divides(u,n) 这种把手而顺利通过——对照着看,触发器的道理就活了。

## divides-forall.dfy：循环的 forall 刻画

**这个文件的主旨**:写程序时常用递归/循环逐个检查一串东西;写规格时想说的却是一句干净的数学话:"对这个范围里的一切 u,性质成立。"本文件示范如何证明二者等价——递归检查器 primeCheck 恰好等价于一条 forall。**这是 forall 真正的用武之地:给循环一个不提循环的、纯逻辑的刻画。**

divides(m, n):m 整除 n 吗?一般情形用取模判断 n % m == 0。m == 0 单独处理,因为 n % 0 在数学上未定义、在 Dafny 里直接是验证错误——**这个 if 不是风格选择,是给 % 站岗的卫兵**。(约定 0 只整除 0:唯一能写成 0×k 的数是 0。)

primeCheck(t, n):一台从 t 开始**倒着数的检查机**——t 整除 n 吗?t-1 呢?……一路查到 2 为止(1 整除一切,不查)。全都不整除,返回 true。**短路语义帮了终止的忙**:t ≤ 1 为真时 || 右边不再求值,递归只在 t ≥ 2 时发生,t-1 严格递减,结构上安然终止。requires 1 < n 是被检数的门槛(0 和 1 谈不上素性检查)。

```dafny
predicate divides(m:nat, n:nat)
{
    if m == 0 then n == 0
    else n % m == 0
}

// checks if t and all numbers below it *don't* divide into n.
// when/if t gets as far as 1, then return true, as we've checked
// everything down to that point
predicate primeCheck(t : nat, n : nat )
  requires 1 < n
{
    t <= 1 || (!divides(t,n) && primeCheck(t - 1, n))
}
```

一条测试型 lemma:具体数字代入,Dafny 直接把递归算穿。35 = 5×7 明明不是素数,但只查 4、3、2 当然全过——这条测试的价值恰恰是提醒:**primeCheck 的语义是"t 以下无因子",不是"n 是素数"。规格要说它实际做的事。**

```dafny
// (4,35) should return true, even though 35 is not prime
// because it only checks to see if 4, 3 or 2 divide into
// 35, and none of them do.
lemma primeCheck_4_35()
  ensures primeCheck(4,35) {}
```

**正片。** 读作:对任意 t、n(n > 1),primeCheck(t,n) 为真 ⟺ 对一切满足 1 < u ≤ t 的 u,u 都不整除 n。左边是一台倒数的递归机器,右边是一句对整段范围的静态断言,**定理说两者是同一回事——"循环的 forall 刻画"**。

**竖线语法实战**:`forall u | 1 < u <= t :: !divides(u,n)`,竖线后是圈定范围的前置条件,等价于蕴含式 `forall u :: 1 < u <= t ==> !divides(u,n)`,两种写法随意换。

**为什么空体就过了?两个条件凑齐**:①**把手充足**——!divides(u,n) 是现成的触发器,求解器知道拿哪些 u 去实例化(对照 smallestExists 的裸 s <= m);②**自动归纳**——Dafny 对 lemma 参数默认尝试归纳,沿 t 的归纳假设恰好对上 primeCheck 的递归结构。于是这条看着吓人的 iff 白送。

**体内那行被注释的 assert 的故事**:讲师课上现场翻车——同一个事实,作为 ensures 能自动证出,作为 assert 写在体内反而报错。这不是操作有误,是触发器机制的喜怒无常:assert 引入的量词实例化路径和 ensures 的不同,脆弱性就显形了。留着这行注释当纪念碑:**量词证明"能过"与"稳过"是两回事,同义改写可能改变生死。**

```dafny
lemma primeCheck_forall(t: nat, n:nat)
  requires 1 < n
  ensures primeCheck(t,n) <==>
          forall u | 1 < u <= t :: !divides(u,n)
{
  // assert forall u:nat :: 1 < u <= t ==> !divides(u,n);
}
```

讲义结尾的预告:subset 那台"逐个查成员"的递归机器,和 primeCheck 是**同一个物种**,也该有它的 forall 刻画——竖线式与蕴含式各写一遍,这正是下一个文件的开场白:

```dafny
subset(A,B) <==> forall x | member(x,A) :: member(x,B)
           <==> forall x :: member(x,A) ==> member(x,B)
```

## subset-forall.dfy：压轴,苦役一笔勾销

**剧情梗概**:第九课里证 subset_refl 何等狼狈——直接归纳撞墙,被迫另立 subset_widen 搭桥。本文件先证大定理 **subset(A,B) ⟺ forall x | member(x,A) :: member(x,B)**,即"我们那台逐个检查的 subset 机器,与数学家的子集定义完全等价"。一旦它在手,**subset_refl 塌缩成一行**:因为 member(x,A) ⟹ member(x,A) 是废话真理,连 Dafny 都秒懂。**表达力换来的证明力,这是 forall 的分红。**

※ 原文件仅 reverse_subset 空体不可过(3 个 postcondition 错误),补全见文末。全文件 Dafny 4.11.0 实测:**8 verified, 0 errors**。

三件旧物:member 查成员,subset 逐个查包含;member_append 说**拼接不改成员资格**——就是 lecture08_01 里那条 member_union(union 委托 append),空体即过,稍后 reverse 的证明要用它(本文件要求 core-list.dfy 提供 append;若没有,把标准定义补进去)。reverse 反转列表:递归反转尾巴,再把头以单元素表 [x] 的身份拼到末尾,朴素的 O(n²) 写法,教学用足够。

```dafny
include "../core-list.dfy"

/* preliminaries: definitions of member, subset and reverse,
   and a useful result about being a member of append (see
   before when we were showing properties of union) */

predicate member(x:int, A:lset)
{
    match A
    case Nil => false
    case Cons(y,ys) => x == y || member(x,ys)
}

predicate subset(A: lset, B : lset)
{
    match A
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}

lemma member_append(x:int, A:lset, B : lset)
  ensures member(x,append(A,B)) <==> member(x,A) || member(x,B)
{}

function reverse<T>(l : list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
    // in nicer Haskell would be
    //   case l of
    //     []   -> []
    //     x:xs -> reverse xs ++ [x]
}
```

## subset_forall：大定理,难的方向出乎意料

iff 即双向蕴含,证法是**对左边的真假做 if 分岔**——第九课的 case split 直接上岗,只是这次分岔条件是谓词本身。

**⟹ 方向,出乎意料地白送**:subset 为真时要证右边的 forall。这本质就是第九课的 subset_member 定理,Dafny 的自动归纳当场重演了一遍,分支留空即可。

**⟸ 方向(逆否),才是硬仗**:subset 为假时须证右边的 forall 也为假。怎么证一个 forall 为假?——**出示反例**:找到一个具体的 x⋆,它在 A 里、却不在 B 里。**"¬forall = 存在反例"**,量词理论的核心等式,在此第一次实战。

Nil 支不可能:Nil 时 subset 恒真,与 else 分支的入场券 ¬subset 矛盾,Dafny 自己看穿,留空。Cons 支再分岔——subset(Cons(x,xs),B) 为假 = member(x,B) 与 subset(xs,B) 至少一个为假,**反例藏在哪,取决于是哪一个**:

**新语法:`var w :| P;`——"取一个使 P 成立的值"**,读作"存在这样的家伙,抓一个出来命名"。合法的前提是 Dafny 能证明确有此家伙——此处它能:对 (xs,B) 的归纳假设(自动归纳暗中提供的 subset_forall(xs,B))说 ¬subset(xs,B) ⟺ 存在反例于 xs。x0 在 xs 里当然也在 A = Cons(x,xs) 里——反例到手,把它亮给存在量词(**exists 配 &&,铁律再现**)。

```dafny
lemma subset_forall(A : lset, B : lset)
  ensures subset(A,B) <==> forall x | member(x,A) :: member(x,B)
{
    if subset(A,B) {
        // dafny automatically reproves our existing member_subset
    } else {
        /* A not a subset of B */
        match A
        case Nil =>   /* impossible */
        case Cons(x,xs) => {
            if member(x,B) {
                // 头是无辜的，罪证必在尾巴里：
                assert !subset(xs,B);
                var x0 :| member(x0,xs) && !member(x0,B);
                // 反例到手，亮给存在量词：
                assert exists x0 :: member(x0,A) && !member(x0,B);
            } else {
                // 头自己就是罪证：x ∈ A 且 x ∉ B。
                assert member(x,A);
                assert !member(x,B);
            }
        }
    }
    // surprising which is the tricky direction
}
```

"surprising which is the tricky direction"——讲义原话。直觉里"从逐个检查推出 forall"像是难的一边,实际白送;**难的是反方向:否定 forall 必须构造证人,而构造,从来比检验贵**。这个预告直指下一课:存在量词。

## 收割：subset_refl 与 mem_reverse

**收割时刻。** 对照第九课:match、归纳、subset_widen 搭桥,三段式苦役。现在:实例化大定理,把 subset(A,A) 翻译成 forall x | member(x,A) :: member(x,A)——自蕴含,空气般显然。**同一定理的两次人生,差的只是刻画方式。**

```dafny
lemma subset_refl(A:lset)
  ensures subset(A,A)
{
    subset_forall(A,A);
}
```

mem_reverse:**反转不改成员资格**,x ∈ reverse(A) ⟺ x ∈ A。归纳到 Cons(y,ys):reverse(A) == append(reverse(ys), [y]),于是搬 member_append 拆开拼接——x 要么在 reverse(ys) 里(归纳假设:即在 ys 里),要么就是 y,两路合起来恰是 member(x, Cons(y,ys))。**归纳假设由自动归纳暗中供给,体内只需摆出 member_append 这一块拼图。**

```dafny
lemma mem_reverse(x:int, A:lset)
  ensures member(x, reverse(A)) <==> member(x,A)
{
    match A
    case Nil => {}
    case Cons(y,ys) =>
        member_append(x,reverse(ys),Cons(y,Nil));
}
```

## reverse_subset：forall 语句首演

原文件空体不可过,此处为补全的证明——也是本课新语法 **forall 语句**的首演。定理读作:**reverse(A) ⊆ A 且 A ⊆ reverse(A)(互为子集)**。

思路两步走:①想借 subset_forall 把两个 subset 目标都翻译成 forall;②那就得先让"∀x: x ∈ reverse(A) ⟺ x ∈ A"进入事实云。mem_reverse 是**逐点的**(一次一个 x),要把它抬升成 forall,用 **forall 语句**——专门的证明构件:

```dafny
forall x ensures Φ(x) { ...证明 Φ(x) 的语句... }
```

**它长得像公式却是语句**(露馅处:中间是 ensures 不是 ::)。花括号内 x 是可触碰的具体名字,可以对它调 lemma、做分岔;整块通过后,forall x :: Φ(x) 入云。**这正是"x 藏在 forall 底下够不着,需要把它拎出来逐个处理"时的唯一出路。**

```dafny
lemma reverse_subset(A:lset)
  ensures subset(reverse(A), A)
  ensures subset(A, reverse(A))
{
    forall x ensures member(x, reverse(A)) <==> member(x, A) {
        mem_reverse(x, A);   // 对拎出来的这一个 x，实例化逐点定理
    }
    // 事实云中现有 ∀x 版的成员等价，两次实例化大定理收工：
    subset_forall(reverse(A), A);
    subset_forall(A, reverse(A));
}
```
