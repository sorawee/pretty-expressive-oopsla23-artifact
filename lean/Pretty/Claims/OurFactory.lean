import Pretty.Defs.Factory
import Pretty.Tactic

/-!
## The cost factory for SnowWhite
-/

def maxw : ℕ := 80 

/--
The cost factory for SnowWhite (Section 6) along with proofs that 
the operations satisfy the contracts imposed by the cost factory interface.
-/
def ourFactory : Factory (ℕ × ℕ) := 
  {
    le := fun ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩ => 
      if sumo₁ = sumo₂ then 
        h₁ ≤ h₂ 
      else 
        sumo₁ < sumo₂,

    concat := fun ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩ => ⟨sumo₁ + sumo₂, h₁ + h₂⟩,
    
    text := fun c l => 
      let a := (max maxw c) - maxw 
      let b := c + l - (max maxw c)
      ⟨b * (2 * a + b), 0⟩,

    nl := fun _ => ⟨0, 1⟩,
    W := 100,

    text_monotonic := by {
      intros c c' l hc 
      simp 
      by_cases h_l : l > 0 
      case pos => 
        by_cases h_if0 : c = c' 
        case pos => simp [h_if0]
        case neg => 
          have h_lt : c < c' := by {
            simp at h_if0 
            cases hc 
            case refl => simp at h_if0
            case step => 
              simp_arith at *
              assumption
          }
          clear hc h_if0
          by_cases h_if : c ≥ maxw
          case pos => 
            have h_if' : c' ≥ maxw := by linarith
            simp [h_if, h_if']
            intro h 
            apply Nat.mul_lt_mul_of_pos_left
            case h => 
              apply Nat.add_lt_add_right
              apply Nat.mul_lt_mul_of_pos_left
              case h => 
                clear h h_l
                dwi { apply Nat.sub_lt_sub_right }
              case hk => simp
            case hk => assumption
          case neg => 
            simp at h_if 
            have h_max : max maxw c = maxw := by {
              simp 
              apply Nat.le_of_lt
              assumption
            }
            simp [h_max]
            by_cases h_if' : c' ≥ maxw
            case pos => 
              simp [h_if']
              intro _
              have : c + l - maxw < l := by {
                clear * - h_if h_l
                rw [Nat.add_comm, Nat.sub_sub_eq]
                . generalize h : maxw - c = v 
                  cases v 
                  case zero => 
                    simp at h
                    linarith
                  case succ => 
                    clear * - h_l
                    cases l 
                    case zero => simp at h_l 
                    case succ => simp_arith
                . apply Nat.le_of_lt
                  assumption
              }
              have this2 : c + l - maxw < 2 * (c' - maxw) + l := by linarith
              dwi { apply Nat.mul_lt_mul₀ }
            case neg => 
              simp at h_if'
              have h_max' : max maxw c' = maxw := by {
                simp 
                apply Nat.le_of_lt
                assumption
              }
              simp [h_max']
              intro h 
              apply Nat.mul_self_lt_mul_self
              by_cases h_if'' : c + l ≥ maxw
              case pos => 
                have h_if''' : c' + l ≥ maxw := by linarith
                clear * - h_if''' h_if'' h_lt
                dwi { apply Nat.sub_lt_sub_right }
                simpa
              case neg => 
                simp at h_if''
                have : c + l - maxw = 0 := by {
                  simp
                  apply Nat.le_of_lt
                  assumption
                }
                by_cases h_if''' : c' + l > maxw 
                case pos => 
                  simp [this]
                  simp at h_if''' 
                  assumption
                case neg => 
                  simp at h_if'''
                  have : c' + l - maxw = 0 := by {
                    simpa
                  }
                  simp [*] at h
      case neg => 
        intro h
        simp at h_l 
        simp [h_l] at h 
    },

    nl_monotonic := by simp,
    concat_monotonic := by {
      intro ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩ ⟨sumo₃, h₃⟩ ⟨sumo₄, h₄⟩
      simp 
      split_ifs 
      case inl.inl.inl | inr.inr.inl | inr.inr.inr | inr.inl.inr => 
        intro h1 h2 
        linarith
      case inl.inl.inr | inl.inr.inl | inl.inr.inr | inr.inl.inl => 
        simp [*] at *
    },
    le_trans := by {
      intro ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩ ⟨sumo₃, h₃⟩
      simp
      split_ifs 
      case inl.inl.inl | inr.inr.inl | inr.inr.inr | inr.inl.inr => 
        intro h1 h2 
        linarith
      case inl.inl.inr | inl.inr.inl | inl.inr.inr | inr.inl.inl => 
        simp [*] at *
    },
    le_antisymm := by {
      intro ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩
      simp
      split_ifs
      case inl.inl h => 
        intro h1 h2 
        simp [h]
        dwi { apply Nat.le_antisymm }
      case inl.inr | inr.inl => 
        simp [*] at *
      case inr.inr => 
        intro h1 h2 
        linarith
    }
    le_total := by {
      intro ⟨sumo₁, h₁⟩ ⟨sumo₂, h₂⟩
      simp
      split_ifs
      case inl.inl => apply Nat.le_total
      case inl.inr | inr.inl | inr.inr => simp [*] at *
    }
  }