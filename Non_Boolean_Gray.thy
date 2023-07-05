(*
  Author: Maximilian Spitz
*)

theory Non_Boolean_Gray imports Code_Word_Dist begin


section \<open>A non-Boolean Gray code\<close>

fun to_gray :: "BASE \<Rightarrow> word \<Rightarrow> word" where
  "to_gray _ [] = []"
| "to_gray b (a#v) = (let g=to_gray b v in dist1 b (sum_list g mod b) a#g)"

fun decode :: "BASE \<Rightarrow> word \<Rightarrow> word" where
  "decode _ [] = []"
| "decode b (g#c) = (g+sum_list c mod b) mod b#decode b c"


section \<open>Correctness Proof\<close>

lemma length_gray:
  "length (to_gray b w) = length w"
  apply (induction w)
  by (auto simp add: Let_def)

lemma valid_gray:
  "valid b w \<Longrightarrow> valid b (to_gray b w)"
  apply (induction w)
  by (auto simp add: dist1_valid Let_def)

lemma prefix_sum:
  "valid b w \<Longrightarrow> sum_list (to_gray b w) mod b = val b w mod b"
proof (induction w)
  case Nil thus ?case by simp
next
  case (Cons a w)
  hence IH: "sum_list (to_gray b w) mod b = val b w mod b" by simp
  let ?s = "sum_list (to_gray b w)"
  let ?v = "val b w mod b"
  have "(dist1 b ?v a + ?s) mod b = (dist1 b ?v a + ?s mod b) mod b" by presburger
  also have "... = (dist1 b ?v a + ?v) mod b" using IH by argo
  also have "... = a" using Cons.prems dist1_elim_1 by simp
  finally show ?case using Cons by auto
qed

lemma decode_correct:
  "valid b w \<Longrightarrow> decode b (to_gray b w) = w"
  apply (induction w)
  by (auto simp add: Let_def dist1_elim_1)

theorem gray_encoding:
  "inj_on (to_gray b) {w. valid b w}"
proof (rule inj_on_inverseI)
  fix w :: word
  assume "w \<in> {w. valid b w}"
  hence "valid b w" by blast
  thus "decode b (to_gray b w) = w" using decode_correct by simp
qed

lemma mod_mod_aux: "1 \<le> k \<Longrightarrow> (a::nat) mod b^k mod b = a mod b"
  by (simp add: mod_mod_cancel)

lemma gray_dist:
  "valid b w \<Longrightarrow> dist b (to_gray b w) (to_gray b (inc b w)) \<le> 1"
proof (induction w)
  case Nil thus ?case by simp
next
  case (Cons a w)
  have "valid b w" using Cons.prems by simp
  hence "2 \<le> b" using valid_base by auto
  hence "0 < b" by simp
  have IH: "dist b (to_gray b w) (to_gray b (inc b w)) \<le> 1"
    using \<open>valid b w\<close> Cons.IH by blast
  have "a < b" using Cons.prems by simp
  show ?case
  proof (cases w)
    case Nil thus ?thesis
      using dist1_distr dist1_Suc \<open>a < b\<close> \<open>2 \<le> b\<close> by simp
  next
    case (Cons a' ds')
    hence "1\<le>length(w)" by simp
    let ?a = "if Suc a\<noteq>b then w else inc b w"
    let ?g = "sum_list (to_gray b w) mod b"
    let ?h = "sum_list (to_gray b ?a) mod b"
    let ?v = "val b w mod b"
    let ?u = "val b ?a mod b"
    let ?l = "dist b (to_gray b (a#w)) (to_gray b (inc b (a#w)))"
    have "valid b ?a" using \<open>valid b w\<close> valid_inc by simp
    have "?l = dist1 b (dist1 b ?g a) (dist1 b ?h (Suc a mod b))
             + dist b (to_gray b w) (to_gray b ?a)"
      by (metis Encoding_Nat.inc.simps(2) dist.simps(4) to_gray.simps(2))
    also have "... = Suc (dist1 b (dist1 b ?g a) (dist1 b ?h a)) mod b
             + dist b (to_gray b w) (to_gray b ?a)"
      using \<open>a < b\<close> dist1_mod_Suc dist1_valid by simp
    also have "... = Suc (dist1 b ?h ?g) mod b
             + dist b (to_gray b w) (to_gray b ?a)"
      using \<open>a < b\<close> dist1_distr2 by simp
    also have "... = Suc (dist1 b ?h ?v) mod b
             + dist b (to_gray b w) (to_gray b ?a)"
      using \<open>valid b w\<close> prefix_sum by simp
    also have "... = Suc (dist1 b ?u ?v) mod b
             + dist b (to_gray b w) (to_gray b ?a)"
      using \<open>valid b ?a\<close> prefix_sum by simp
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else Suc (dist1 b (val b (inc b w) mod b) ?v) mod b
             + dist b (to_gray b w) (to_gray b (inc b w)))"
      using dist_0 dist1_0 by simp
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else Suc (dist1 b (Suc (val b w) mod b^length(w) mod b) ?v) mod b
             + dist b (to_gray b w) (to_gray b (inc b w)))"
      using \<open>valid b w\<close> valid_inc val_inc by simp
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else Suc (dist1 b (Suc (val b w) mod b) ?v) mod b
             + dist b (to_gray b w) (to_gray b (inc b w)))"
      using \<open>1\<le>length(w)\<close> mod_mod_aux by simp
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else dist1 b (Suc (val b w) mod b) (Suc ?v mod b)
             + dist b (to_gray b w) (to_gray b (inc b w)))"
      using dist1_mod_Suc by auto
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else dist1 b (Suc ?v mod b) (Suc ?v mod b)
             + dist b (to_gray b w) (to_gray b (inc b w)))"
      using mod_Suc_eq by presburger
    also have "... = (
        if Suc a \<noteq> b then Suc 0 mod b
        else dist b (to_gray b w) (to_gray b (inc b w)))"
      using dist1_0 by simp
    also have "... \<le> 1" using IH by simp
    finally show ?thesis by blast
  qed
qed

lemmas gray_simps = decode_correct dist_posd inc_not_eq length_gray length_inc valid_gray valid_inc

lemma gray_empty:
  "valid b w \<Longrightarrow> (dist b (to_gray b w) (to_gray b (inc b w)) = 0) = (w = [])"
  by (metis gray_simps)

theorem gray_correct:
  "\<lbrakk>valid b w; w \<noteq> []\<rbrakk> \<Longrightarrow> dist b (to_gray b w) (to_gray b (inc b w)) = 1"
proof (rule ccontr)
  assume a: "dist b (to_gray b w) (to_gray b (inc b w)) \<noteq> 1"
  assume "valid b w" and "w \<noteq> []"
  hence "dist b (to_gray b w) (to_gray b (inc b w)) \<noteq> 0" using gray_empty by blast
  with a have "dist b (to_gray b w) (to_gray b (inc b w)) > 1" by simp
  thus "False" using \<open>valid b w\<close> gray_dist by fastforce
qed

lemmas hamming_simps = gray_dist hamming_dist le_trans length_gray length_inc valid_gray valid_inc

theorem gray_hamming: "valid b w \<Longrightarrow> hamming (to_gray b w) (to_gray b (inc b w)) \<le> 1"
  by (metis hamming_simps)

end
