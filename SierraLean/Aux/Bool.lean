import Aesop

def Bool.toSierraBool : Bool → Unit ⊕ Unit
| false => .inl ()
| true => .inr ()

def SierraBool.toBool : Unit ⊕ Unit → Bool
| .inl () => false
| .inr () => true

instance : Coe (Unit ⊕ Unit) Bool := ⟨SierraBool.toBool⟩

@[simp] 
theorem SierraBool_toBool_inl : SierraBool.toBool (.inl x) = false := rfl

@[simp]
theorem SierraBool_toBool_inr : SierraBool.toBool (.inr x) = true := rfl

@[simp]
theorem Bool.toSierraBool_true : true.toSierraBool = .inr () := rfl

@[simp]
theorem Bool.toSierraBool_false : false.toSierraBool = .inl () := rfl

@[simp]
theorem Bool.coe_toSierraBool (b : Bool) : (b.toSierraBool : Bool ) = b := by
  cases b <;> simp

@[simp]
theorem Bool.toSierraBool_coe (x : Unit ⊕ Unit) : (x : Bool).toSierraBool = x := by
  rcases x with (x|x) <;> cases x <;> simp

@[simp]
theorem Bool.toSierraBool_decide_inl (p : Prop) [Decidable p] :
    (decide p).toSierraBool = .inl u ↔ ¬ p := by
  aesop

@[simp]
theorem Bool.toSierraBool_decide_inl' (p : Prop) [Decidable p] :
    .inl u = (decide p).toSierraBool ↔ ¬ p := by
  aesop

@[simp]
theorem Bool.toSierraBool_decide_inr (p : Prop) [Decidable p] :
    (decide p).toSierraBool = .inr u ↔ p := by
  by_cases h : p
  · simp [h]
  · simp [h]

@[simp]
theorem Bool.toSierraBool_decide_inr' (p : Prop) [Decidable p] :
    .inr u = (decide p).toSierraBool ↔ p := by
  by_cases h : p
  · simp [h]
  · simp [h]
