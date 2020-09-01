theory NoDups imports Main
begin

(*
  Predicates capturing sorted and no-duplicates
  Isabelle/HOL has two ways of expressing logical statements,
  an "outer" language using \<And> quantifiers and \<Longrightarrow> implication,
  and an "inner" language using \<forall> and \<longrightarrow>
  Here I define sortedness and uniqueness predicates in the inner language,
  and then define some rules for reasoning about them at the outer-language level
  (which is convenient for structured proofs).
  I think there is a more automated way to do this conversion.
*)
definition nodups :: "int list \<Rightarrow> bool" where
"nodups l = (\<forall> x y .
  0 \<le> x \<longrightarrow> 0 \<le> y \<longrightarrow>
  x < length l \<longrightarrow> y < length l \<longrightarrow>
  List.nth l x = List.nth l y \<longrightarrow> x = y)"

lemma nodups_intro :
"(\<And> x y .
  0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow>
  x < length l \<Longrightarrow> y < length l \<Longrightarrow>
  List.nth l x = List.nth l y \<Longrightarrow> x = y) \<Longrightarrow> nodups l"
  unfolding nodups_def by auto

lemma nodups_elim :
  "nodups l \<Longrightarrow>
  0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow>
  x < length l \<Longrightarrow> y < length l \<Longrightarrow>
  List.nth l x = List.nth l y \<Longrightarrow> x = y"
  unfolding nodups_def by auto

definition sorted :: "int list \<Rightarrow> bool" where
"sorted l = (\<forall> x y  .
  0 \<le> x \<longrightarrow> x < y \<longrightarrow>
  y < length l \<longrightarrow>
  List.nth l x \<le> List.nth l y)"

lemma sorted_intro :
"(\<And> x y  .
  0 \<le> x \<Longrightarrow> x < y \<Longrightarrow>
  y < length l \<Longrightarrow>
  List.nth l x \<le> List.nth l y) \<Longrightarrow> sorted l"
  unfolding sorted_def by auto

lemma sorted_elim :
"sorted l \<Longrightarrow>
  0 \<le> x \<Longrightarrow> x < y \<Longrightarrow>
  y < length l \<Longrightarrow>
  List.nth l x \<le> List.nth l y"
  unfolding sorted_def by auto

fun removeDups :: "int list \<Rightarrow> int list" where
"removeDups [] = []"
| "removeDups [x] = [x]"
| "removeDups (h1#h2#t) =
   (if h1 = h2 then removeDups (h1 # t)
    else h1 # removeDups (h2 # t))"

(* sortedness-related lemmas 
   NB the standard library contains an implementation of sorted with an associated library
   of lemmas, but I chose not to use them for the purposes of the exercise.*)
lemma sorted_tl :
  assumes H : "sorted (h#l)"
  shows "sorted l"
proof(cases l)
  case Nil
  then show ?thesis by(auto simp add:sorted_def)
next
  case (Cons a list)
  show ?thesis
  proof(rule sorted_intro)
    fix x :: nat
    fix y :: nat
    assume H1 : "0 \<le> x" 
    assume H2 : "x < y" 
    assume H3 : "y < length l"
    show "l ! x \<le> l ! y"
      using sorted_elim[OF H,of "1 + x" "1 + y"] H2 H3 by auto
  qed
qed

lemma sorted_tl2 :
  assumes H : "sorted (h1 # h2 #l)"
  shows "sorted (h1 # l)"
proof(cases l)
  case Nil
  then show ?thesis by(auto simp add:sorted_def)
next
  case (Cons a list)
  show ?thesis
  proof(rule sorted_intro)
    fix x :: nat
    fix y :: nat
    assume H1 : "0 \<le> x" 
    assume H2 : "x < y" 
    assume H3 : "y < length (h1 # l)"

    have "h1 \<le> h2" using sorted_elim[OF H,of 0 1] by auto

    show "(h1 # l) ! x \<le> (h1 # l) ! y"
    proof(cases x)
      case 0
      then show ?thesis
      proof(cases y)
        assume Z' : "y = 0"
        thus ?thesis using 0 by auto
      next
        fix y'
        assume Suc' : "y = Suc y'"
        then show ?thesis using sorted_elim[OF H, of 0 "1 + y"] 0 H3 by(auto)
      qed
    next
      case (Suc nat)
      then show ?thesis
      proof(cases y)
        assume Z' : "y = 0"
        thus ?thesis using Suc H2 by auto
      next
        fix y'
        assume Suc' : "y = Suc y'"
        then show ?thesis using sorted_elim[OF H, of "1 + x" "1 + y"] Suc H2 H3 by(auto)
      qed
    qed
  qed
qed

(* removeDups related lemmas*)
lemma removeDups_len :
  "1 \<le> length (removeDups (h#l))"
proof(induction l arbitrary: h)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    by(auto)
qed

lemma removeDups_hd :
  "\<exists> l' . removeDups(h#l) = (h#l')"
proof(induction l arbitrary: h)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by(auto)
qed

(* sorted list remains sorted after removing duplicates*)
lemma removeDups_sort :
shows "sorted (h # l) \<Longrightarrow> sorted (removeDups (h # l))"
proof(induction l arbitrary: h)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
  proof(cases "h = a")
    case True

    have "sorted (a # l)" using sorted_tl[OF Cons(2)] by auto
    then show ?thesis
      using Cons True by(auto)
  next
    case False

    have St1 : "sorted (h # l)" using sorted_tl2[OF Cons(2)] by auto
    have St2 : "sorted (removeDups (h#l))"
      using Cons.IH[OF St1] by auto

    have St3 : "sorted (a # l)" using sorted_tl[OF Cons(2)] by auto
    have St4 : "sorted (removeDups (a#l))"
      using Cons.IH[OF St3] by auto


    show ?thesis
    proof(rule sorted_intro)
      fix x :: nat
      fix y :: nat
      assume H1 : "0 \<le> x"
      assume H2 : "x < y"
      assume H3 : "y < length (removeDups (h # a # l))"
      
      show "removeDups (h # a # l) ! x \<le> removeDups (h # a # l) ! y"
      proof(cases x)
        case 0
        then show ?thesis
        proof(cases y)
          assume Z' : "y = 0"
          then show ?thesis using 0 H2 by auto
        next
          fix y'
          assume Suc' : "y = Suc y'"

          have H_lt_a : "h \<le> a" using sorted_elim[OF Cons(2), of 0 1] by(auto)

          show ?thesis
          proof(cases y')
            assume Z'' : "y' = 0"
            
            have "a = removeDups (a # l) ! 0"
              using removeDups_hd[of a l] by auto

            thus ?thesis using 0 Z'' Suc' False H_lt_a by(auto)
          next
            fix y''
            assume Suc'' : "y' = Suc y''"

            have "a \<le> removeDups (a # l) ! Suc y''"
              using sorted_elim[OF St4, of 0 "Suc y''"] 
                    removeDups_hd[of a l]
                    removeDups_len[of h "(a # l)"] Suc' Suc'' H3 False
              by(auto)
            then show ?thesis using 0 Suc'' Suc' False St4 H_lt_a
              by(auto)
          qed
        qed
      next
        case (Suc x')
        then show ?thesis
        proof(cases y)
          assume Z' : "y = 0"
          then show ?thesis using Suc H2 by auto
        next
          fix y'
          assume Suc' : "y = Suc y'"
          show ?thesis
            using sorted_elim[OF St4, of x' y'] Suc Suc' H2 H3 False
            by(auto) 
        qed
      qed
    qed
  qed
qed

(* Main result: running RemoveDups results in a list with no duplicates *)
lemma removeDups_nodups' :
  shows "sorted (h # l) \<Longrightarrow> nodups (removeDups (h # l))"
proof(induction l arbitrary: h)
case Nil
  then show ?case apply(auto simp add:sorted_def nodups_def) done
next
  case (Cons a l)
  have Sort1 : "sorted (a # l)" using sorted_tl[OF Cons(2)] by auto

  have Sort2 : "sorted (h # l)" using sorted_tl2[OF Cons(2)] by auto

  have Leq : "h \<le> a" using sorted_elim[OF Cons(2), of 0 1] by auto

  show ?case 
  proof(cases "h = a")
    case True
    then show ?thesis using Cons.IH[OF Sort1] by auto
  next
    case False
    show ?thesis
    proof(rule nodups_intro)
      fix x :: nat
      fix y :: nat
      assume Hx : "0 \<le> x"
      assume Hy : "0 \<le> y"
      assume Xlen : "x < length (removeDups (h # a # l))"
      assume Ylen : "y < length (removeDups (h # a # l))" 
      assume El_eq : "removeDups (h # a # l) ! x = removeDups (h # a # l) ! y"
      show "x = y"
      proof(cases x)
        case 0
        then show ?thesis
        proof(cases y)
          assume Z' : "y = 0"
          show "x = y" using 0 Z' by auto
        next
          fix y'
          assume Suc' : "y = Suc y'"
          then have False
          proof(cases "h = a")
            case True
            then show ?thesis using El_eq 
                 nodups_elim[OF Cons.IH[OF Sort1], of 0 y] 0 Suc' Xlen Ylen by(auto)
          next
            case False
            then show ?thesis 
            proof(cases y')
              assume Z'' : "y' = 0"
              obtain l' where L' : "removeDups(a#l) = (a#l')"
                using removeDups_hd by auto
              then show ?thesis using El_eq 0 Cons Suc' False Z'' by(auto)
            next
              fix y''
              assume Suc'' : "y' = Suc y''"

              have St : "sorted (removeDups (a#l))"
                    using removeDups_sort[OF Sort1] by auto

              have Leq' : "a \<le> removeDups (a # l) ! Suc y''" using 
                  sorted_elim[OF St, of 0 "Suc y''"]
                  removeDups_hd[of a l]
              Xlen Ylen Suc' Suc'' False
              by(auto)


            have St' : "sorted (removeDups (a # l) ! y' # a # l)"
              using El_eq 0 Cons Suc' False by(auto)
            show ?thesis using sorted_elim[OF St', of 0, of 1]
                El_eq 0 Cons Suc' False Leq' Suc''
              by(auto)
            qed
          qed
          thus ?thesis by auto
        qed
      next
        case (Suc x')
        then show ?thesis
        proof(cases y)
          assume Z' : "y = 0"
          then have False
          proof(cases "h = a")
            case True
            then show ?thesis using El_eq 
                 nodups_elim[OF Cons.IH[OF Sort1], of 0 x] Suc Z' Xlen Ylen by(auto)
          next
            case False
            then show ?thesis 
            proof(cases x')
              assume Z'' : "x' = 0"
              obtain l' where L' : "removeDups(a#l) = (a#l')"
                using removeDups_hd by auto
              then show ?thesis using El_eq Suc Cons Z' False Z'' by(auto)
            next
              fix x''
              assume Suc'' : "x' = Suc x''"
              have St : "sorted (removeDups (a#l))"
                    using removeDups_sort[OF Sort1] by auto

              have Leq' : "a \<le> removeDups (a # l) ! Suc x''" using 
                  sorted_elim[OF St, of 0 "Suc x''"]
                  removeDups_hd[of a l]
                  removeDups_len[of a l]
              Xlen Ylen Suc Suc'' Z' False
                by(auto)
              have St' : "sorted (removeDups (a # l) ! Suc x'' # a # l)"
                using El_eq Suc Z' Cons Suc'' False by(auto)
              show ?thesis using sorted_elim[OF St', of 0, of 1]
                  El_eq Suc Z' Cons False Leq' Suc''
                by(auto)
              qed
            qed
            thus ?thesis by auto
        next
          fix y'
          assume Suc' : "y = Suc y'"
          thus ?thesis using El_eq  Suc
            nodups_elim[OF Cons.IH[OF Sort1]] Xlen Ylen
            by(auto split:if_splits)
        qed
      qed
    qed
  qed
qed

(* general version of the theorem (holds for nil lists too) *)
theorem removeDups_nodups :
  assumes H : "sorted l"
  shows "nodups (removeDups (l))"
proof(cases l)
case Nil
  then show ?thesis by (auto simp add:nodups_def)
next
  case (Cons a list)
  then show ?thesis using removeDups_nodups' H by auto
qed

end