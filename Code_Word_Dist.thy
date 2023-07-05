(*
  Author: Maximilian Spitz
*)

theory Code_Word_Dist imports Encoding_Nat begin


section \<open>Distance for Digits\<close>


(* dist1 b x y ~ y-x in the additive group of the factor ring \<int> modulo (b) *)
definition dist1 :: "BASE \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dist1 b x y \<equiv> if x\<le>y then y-x else b+y-x"

lemma dist1_0:
  "dist1 b x x = 0"
  by (auto simp add: dist1_def)

lemma dist1_eq:
  "\<lbrakk>x < b; y < b; dist1 b x y = 0\<rbrakk> \<Longrightarrow> x = y"
  by (auto simp add: dist1_def split: if_splits)

lemma dist1_ge1:
  "\<lbrakk>x < b; y < b; x\<noteq>y\<rbrakk> \<Longrightarrow> dist1 b x y \<ge> 1"
  using dist1_eq by fastforce

lemma dist1_elim_1:
  "\<lbrakk>x < b; y < b\<rbrakk> \<Longrightarrow> (dist1 b x y + x) mod b = y"
  by (auto simp add: dist1_def)

(* y instead of y mod b*)
lemma dist1_elim_2:
  "\<lbrakk>x < b; y < b\<rbrakk> \<Longrightarrow> dist1 b x (x+y) = y"
  by (auto simp add: dist1_def)

lemma dist1_mod_Suc:
  "\<lbrakk>x < b; y < b\<rbrakk> \<Longrightarrow> dist1 b x (Suc y mod b) = Suc (dist1 b x y) mod b"
  by (auto simp add: dist1_def mod_Suc)

lemma dist1_Suc:
  "\<lbrakk>2 \<le> b; x < b\<rbrakk> \<Longrightarrow> dist1 b x (Suc x mod b) = 1"
  by (simp add: dist1_0 dist1_mod_Suc)

lemma dist1_asym:
  "\<lbrakk>x < b; y < b\<rbrakk> \<Longrightarrow> (dist1 b x y + dist1 b y x) mod b = 0"
  by (auto simp add: dist1_def)

lemma dist1_valid:
  "\<lbrakk>x < b; y < b\<rbrakk> \<Longrightarrow> dist1 b x y < b"
  by (auto simp add: dist1_def)

(* TODO: Emin fragen: linarith_split_limit exceeded *)
lemma dist1_distr:
  "\<lbrakk>x < b; y < b; z < b\<rbrakk> \<Longrightarrow> dist1 b (dist1 b x y) (dist1 b x z) = dist1 b y z"
  by (auto simp add: dist1_def)

lemma dist1_distr2:
  "\<lbrakk>x < b; y < b; z < b\<rbrakk> \<Longrightarrow> dist1 b (dist1 b x z) (dist1 b y z) = dist1 b y x"
  by (auto simp add: dist1_def)


section \<open>(Hamming-)Distance for Words\<close>


fun hamming :: "word \<Rightarrow> word \<Rightarrow> nat" where
  "hamming [] [] = 0"
| "hamming (a#v) (b#w) = (if a\<noteq>b then 1 else 0) + hamming v w"

fun dist :: "BASE \<Rightarrow> word \<Rightarrow> word \<Rightarrow> nat" where
  "dist _ [] [] = 0"
| "dist b (x#xs) [] = dist1 b x 0 + dist b xs []"
| "dist b [] (y#ys) = dist1 b 0 y + dist b [] ys"
| "dist b (x#xs) (y#ys) = dist1 b x y + dist b xs ys"

lemma dist_0:
  "dist b w w = 0"
  apply (induction w)
  by (auto simp add: dist1_0)

lemma dist_eq:
  "\<lbrakk>valid b v; valid b w; length v=length w; dist b v w = 0\<rbrakk> \<Longrightarrow> v = w"
  apply (induction b v w rule: dist.induct)
  by (auto simp add: dist1_eq)

lemma dist_posd:
  "\<lbrakk>valid b v; valid b w; length v=length w\<rbrakk> \<Longrightarrow> (dist b v w = 0) = (v = w)"
  using dist_0 dist_eq by auto

lemma hamming_posd:
  "length v=length w \<Longrightarrow> (hamming v w = 0) = (v = w)"
  by (induction v w rule: hamming.induct) auto

lemma hamming_symm:
  "length v=length w \<Longrightarrow> hamming v w = hamming w v"
  by (induction v w rule: hamming.induct) auto

theorem hamming_dist:
  "\<lbrakk>valid b v; valid b w; length v=length w\<rbrakk> \<Longrightarrow> hamming v w \<le> dist b v w"
  apply (induction b v w rule: dist.induct)
     apply auto
  using dist1_ge1 by fastforce

end
