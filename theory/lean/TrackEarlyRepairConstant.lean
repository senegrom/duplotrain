import TrackStayContactAllTime

/-!
# Constant vector counts for protected backward contacts

A protected repair prefix has two phases.  Once a backward contact is taken,
the retrace/replay cycle has only the incoming contact vector and its settled
post-contact vector.  The whole branch therefore has at most three vectors.
-/

namespace GeneralN

/-- Starting at the contact itself, a backward retrace/replay cycle has at
most two distinct restricted tongue vectors. -/
theorem backward_contact_tail_distinct_le_two
    {w : Wiring} {N g e p oldEntry : Nat}
    {oldBase oldEnd u v : Tongues}
    {recorded approach : List Passage}
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, u) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (p, u))).Nodup) :
    times.length ≤ 2 := by
  have hall := backward_contact_all_time_two_phase hrecorded hrecordedGrooved
    hentry hcontact happroach happroachGrooved
  have hcover : NoveltyCoverOn w N (p, u) times [] 2 := by
    refine ⟨[VectorCount.restrict N u, VectorCount.restrict N v], by simp, ?_⟩
    intro d _hd
    obtain ⟨port, phase, hr, hp⟩ := hall d
    rcases hp with rfl | rfl <;> simp [restrictedTonguesAt, tonguesAt, hr]
  simpa using noveltyCoverOn_distinct_count hcover hnd

end GeneralN
