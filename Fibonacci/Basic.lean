def hello := "world"



theorem explosion (φ α : Prop) :
    ¬ φ → (φ → α) :=
  fun hNotφ => fun hφ => False.elim (hNotφ hφ)
