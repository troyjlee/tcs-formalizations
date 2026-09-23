import Mathlib.Tactic

/-!
# Independent probability budgets for the §5 disjunction

The common 2-1-1 threshold and the absolute 2-2-2 fallback are distinct.
The first alternative records the recovered KKO route; the second records
the capacity-based improvement. Keeping both preserves the old public APIs.
-/
namespace TSPGap

def Section5Budget (ε p q : ℝ) : Prop :=
  (p ≤ 0.005 * ε ^ 2 ∧ q ≤ 0.005) ∨
  (p ≤ 0.02 * ε ^ 2 ∧ q ≤ 0.0005)

namespace Section5Budget

theorem recovered (ε : ℝ) : Section5Budget ε (0.005 * ε ^ 2) 0.005 :=
  Or.inl ⟨le_rfl, le_rfl⟩

theorem capacity (ε : ℝ) : Section5Budget ε (0.02 * ε ^ 2) 0.0005 :=
  Or.inr ⟨le_rfl, le_rfl⟩

theorem le_common {ε p q : ℝ} (h : Section5Budget ε p q) : p ≤ 0.02 * ε ^ 2 := by
  rcases h with h | h
  · nlinarith only [h.1, sq_nonneg ε]
  · exact h.1

theorem fallback {ε p q a b c : ℝ} (h : Section5Budget ε p q)
    (hold : a < 0.005 * ε ^ 2 → b < 0.005 * ε ^ 2 → 0.005 ≤ c)
    (hnew : a < 0.02 * ε ^ 2 → b < 0.02 * ε ^ 2 → 0.0005 ≤ c)
    (ha : a < p) (hb : b < p) : q ≤ c := by
  rcases h with h | h
  · exact h.2.trans (hold (ha.trans_le h.1) (hb.trans_le h.1))
  · exact h.2.trans (hnew (ha.trans_le h.1) (hb.trans_le h.1))

end Section5Budget
end TSPGap

