(define (problem unity-simple-problem)
  (:domain unity-simple-domain)
  (:objects cowboy bandit - person
            duel-right right far-right - place
            master - virtual-shot-cam
			)
  (:init
		 (bel (at bandit far-right))
		 (bel (bel (at bandit far-right)))
		 (bel (bel (can-show master far-right)))
		 (can-show master far-right)
		 (at bandit far-right)
		 )
  (:goal (and
            (bel (at bandit duel-right))
		 )
  )
)