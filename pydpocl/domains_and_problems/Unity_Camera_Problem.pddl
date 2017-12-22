(define (problem unity-simple-problem)
  (:domain unity-simple-domain)
  (:objects cowboy bandit - person
            far-left left duel-left duel-right right far-right - place
			main-master-shot - virtual-shot-type
			)
  (:init (at cowboy far-left)
		 (at bandit far-right)
		 (bel (at cowboy far-left))
		 (bel (at bandit far-right))
		 (can-show main-master-shot left)
		 (can-show main-master-shot duel-left)
		 (can-show main-master-shot right)
		 (can-show main-master-shot duel-right)
		 )
  (:goal (and
              (bel (at bandit duel-right))
              (bel (at cowboy duel-left))
              (facing cowboy bandit)
              (facing bandit cowboy)
		 )
  )
)