(define (problem unity-simple-problem)
  (:domain unity-simple-domain)
  (:objects cowboy bandit - person
            far-left duel-left duel-right far-right - place
			)
  (:init (at cowboy far-left)
		 (at bandit far-right)
		 (bel (at cowboy far-left))
		 (bel (at bandit far-right))
		 )
  (:goal (and
              (bel (at bandit duel-left))
              (bel (at cowboy duel-right))
              (at cowboy far-right)
		 )
  )
)