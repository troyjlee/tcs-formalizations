import Toda.Counting.AmplificationChoices.Defs

namespace Toda.Counting.AmplificationChoices

open scoped BigOperators

/-- Concatenate a root choice and three child blocks. -/
def joinChoices {n : ℕ} (hn : 0 < n) (b : Bool) (w : Fin 3 → Fin n → Bool) :
    Fin (1 + 3 * n) → Bool :=
  fun i => if h : i.val = 0 then b else
    w ⟨(i.val - 1) / n, (Nat.div_lt_iff_lt_mul hn).mpr (by omega)⟩
      ⟨(i.val - 1) % n, Nat.mod_lt _ hn⟩

/-- Read one child block. -/
def childChoices {n : ℕ} (w : Fin (1 + 3 * n) → Bool) (j : Fin 3) : Fin n → Bool :=
  fun i => w ⟨1 + j.val * n + i.val, by nlinarith [j.isLt, i.isLt]⟩

@[simp] theorem joinChoices_root {n : ℕ} (hn : 0 < n) (b : Bool)
    (w : Fin 3 → Fin n → Bool) : joinChoices hn b w 0 = b := by
  simp [joinChoices]

@[simp] theorem childChoices_joinChoices {n : ℕ} (hn : 0 < n) (b : Bool)
    (w : Fin 3 → Fin n → Bool) : childChoices (joinChoices hn b w) = w := by
  funext j i
  obtain ⟨hdiv, hmod⟩ := child_index hn j.val i
  simp [childChoices, joinChoices, hdiv, hmod]

theorem joinChoices_childChoices {n : ℕ} (hn : 0 < n)
    (w : Fin (1 + 3 * n) → Bool) : joinChoices hn (w 0) (childChoices w) = w := by
  funext i
  simp only [joinChoices]
  split_ifs with hi
  · congr 1
    exact Fin.ext hi.symm
  · simp only [childChoices]
    congr 1
    apply Fin.ext
    change 1 + (i.val - 1) / n * n + (i.val - 1) % n = i.val
    have h := Nat.div_add_mod (i.val - 1) n
    rw [Nat.mul_comm] at h
    omega

/-- Every flat bit string splits uniquely into its root and three child words. -/
def choicesEquiv {n : ℕ} (hn : 0 < n) :
    (Fin (1 + 3 * n) → Bool) ≃ Bool × (Fin 3 → Fin n → Bool) where
  toFun w := (w 0, childChoices w)
  invFun v := joinChoices hn v.1 v.2
  left_inv := joinChoices_childChoices hn
  right_inv v := by simp

/-- Only bits belonging to the subtree affect its activity. -/
theorem nodeActive_congr (k : ℕ) (active : Bool) (u v : List Bool) (i : ℕ)
    (hi : i < nodeCount k)
    (huv : ∀ j < nodeCount k, u[j]?.getD false = v[j]?.getD false) :
    nodeActive k active u i = nodeActive k active v i := by
  induction k generalizing active u v i with
  | zero => rfl
  | succ k ih =>
    by_cases hzero : i = 0
    · simp [nodeActive, hzero]
    · have hroot := huv 0 (nodeCount_pos (k + 1))
      simp only [nodeActive, ite_eq_right hzero, hroot]
      apply ih _ _ _ _ (Nat.mod_lt _ (nodeCount_pos k))
      intro j hj
      simp only [List.getElem?_drop]
      apply huv
      have hdiv : (i - 1) / nodeCount k < 3 :=
        (Nat.div_lt_iff_lt_mul (nodeCount_pos k)).mpr (by simp only [nodeCount] at hi; omega)
      simp only [nodeCount]
      nlinarith

/-- The local factor ignores bits beyond its own tree. -/
theorem localFactor_congr (k : ℕ) (active : Bool) (m : ℤ) (u v : List Bool) (i : ℕ)
    (hi : i < nodeCount k)
    (huv : ∀ j < nodeCount k, u[j]?.getD false = v[j]?.getD false) :
    localFactor k active m u i = localFactor k active m v i := by
  simp only [localFactor, nodeActive_congr k active u v i hi huv, huv i hi]

/-- Restricting a flat choice string to one child gives its exact local factors. -/
theorem localFactor_childChoices (k : ℕ) (active : Bool) (m : ℤ)
    (w : Fin (nodeCount (k + 1)) → Bool) (j : Fin 3) (i : Fin (nodeCount k)) :
    localFactor (k + 1) active m (List.ofFn w) (1 + j.val * nodeCount k + i.val) =
      localFactor k (active && (decide (j.val < 2) || w ⟨0, nodeCount_pos (k + 1)⟩)) m
        (List.ofFn (childChoices w j)) i.val := by
  rw [localFactor_child]
  simp only [List.getElem?_ofFn, dite_eq_left (nodeCount_pos (k + 1)), Option.getD_some]
  apply localFactor_congr _ _ _ _ _ _ i.isLt
  intro t ht
  have hfull : 1 + j.val * nodeCount k + t < nodeCount (k + 1) := by
    simp only [nodeCount]
    nlinarith [j.isLt]
  simp only [List.getElem?_drop, List.getElem?_ofFn, dite_eq_left hfull,
    dite_eq_left ht, Option.getD_some, childChoices]
  rfl

/-- Split a product over the preorder tree into its root and child blocks. -/
theorem prod_nodes {n : ℕ} (f : Fin (1 + 3 * n) → ℤ) :
    (∏ i, f i) = f 0 * ∏ j : Fin 3, ∏ i : Fin n,
      f ⟨1 + j.val * n + i.val, by nlinarith [j.isLt, i.isLt]⟩ := by
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_one]
  congr 1
  rw [← (finProdFinEquiv (m := 3) (n := n)).prod_comp (fun i => f (Fin.natAdd 1 i)),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

/-- The weight of a particular complete choice assignment. -/
def choiceWeight (k : ℕ) (active : Bool) (m : ℤ) (w : Fin (nodeCount k) → Bool) : ℤ :=
  ∏ i : Fin (nodeCount k), localFactor k active m (List.ofFn w) i.val

/-- Product decomposition at an internal node. -/
theorem choiceWeight_succ (k : ℕ) (active : Bool) (m : ℤ)
    (w : Fin (nodeCount (k + 1)) → Bool) :
    choiceWeight (k + 1) active m w = rootFactor active (w ⟨0, nodeCount_pos (k + 1)⟩) *
      ∏ j : Fin 3, choiceWeight k (active && (decide (j.val < 2) || w ⟨0, nodeCount_pos (k + 1)⟩)) m
        (childChoices w j) := by
  unfold choiceWeight
  change (∏ i : Fin (1 + 3 * nodeCount k), localFactor (k + 1) active m (List.ofFn w) i.val) = _
  rw [prod_nodes]
  congr 1
  · change localFactor (k + 1) active m (List.ofFn w) 0 = _
    rw [localFactor_root]
    simp only [List.getElem?_ofFn, dite_eq_left (nodeCount_pos (k + 1)), Option.getD_some]
  · apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    exact localFactor_childChoices k active m w j i

/-- Sum of all signed choice weights at a given depth. -/
def totalWeight (k : ℕ) (active : Bool) (m : ℤ) : ℤ :=
  ∑ w : Fin (nodeCount k) → Bool, choiceWeight k active m w

/-- Independent child choices factor after summation. -/
theorem totalWeight_succ (k : ℕ) (active : Bool) (m : ℤ) :
    totalWeight (k + 1) active m =
      ∑ b : Bool, rootFactor active b * ∏ j : Fin 3,
        totalWeight k (active && (decide (j.val < 2) || b)) m := by
  calc
    totalWeight (k + 1) active m =
        ∑ z : Bool × (Fin 3 → Fin (nodeCount k) → Bool),
          rootFactor active z.1 * ∏ j : Fin 3,
            choiceWeight k (active && (decide (j.val < 2) || z.1)) m (z.2 j) := by
      unfold totalWeight
      apply Fintype.sum_equiv (choicesEquiv (nodeCount_pos k))
      intro w
      exact choiceWeight_succ k active m w
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only
      rw [← Finset.mul_sum, ← Fintype.prod_sum]
      rfl

/-- A depth-zero tree has one canonical leaf choice. -/
theorem totalWeight_zero (active : Bool) (m : ℤ) :
    totalWeight 0 active m = if active then m else 1 := by
  calc
    totalWeight 0 active m = ∑ b : Bool,
        (if active then (if b then 0 else m) else (if b then 0 else 1)) := by
      unfold totalWeight
      apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool)
      intro w
      change (∏ i : Fin 1, localFactor 0 active m (List.ofFn w) i.val) = _
      rw [Fin.prod_univ_one]
      simp [localFactor, nodeActive, nodeLeaf, Equiv.funUnique, Equiv.piUnique]
      rfl
    _ = _ := by cases active <;> simp

/-- Active trees evaluate the amplification iterate; an inactive tree has
exactly one nonzero choice, its all-false assignment. -/
theorem totalWeight_eq (k : ℕ) (active : Bool) (m : ℤ) :
    totalWeight k active m = if active then Arithmetic.amplifyIterate k m else 1 := by
  induction k generalizing active with
  | zero => simpa using totalWeight_zero active m
  | succ k ih =>
    rw [totalWeight_succ]
    simp_rw [ih]
    cases active
    · simp [rootFactor]
    · simp [Fin.prod_univ_three, rootFactor,
        Arithmetic.amplifyIterate_succ, Arithmetic.amplify]
      ring

/-- The signed sum of products equals the integer amplification iterate. -/
theorem sum_prod_localFactor (k : ℕ) (m : ℤ) :
    (∑ bits : Fin (nodeCount k) → Bool, ∏ i : Fin (nodeCount k),
      localFactor k true m (List.ofFn bits) i.val) = Arithmetic.amplifyIterate k m := by
  exact totalWeight_eq k true m

/-- Canonical false choices make an entirely inactive tree contribute one. -/
theorem sum_prod_localFactor_inactive (k : ℕ) (m : ℤ) :
    (∑ bits : Fin (nodeCount k) → Bool, ∏ i : Fin (nodeCount k),
      localFactor k false m (List.ofFn bits) i.val) = 1 := by
  exact totalWeight_eq k false m

end Toda.Counting.AmplificationChoices
