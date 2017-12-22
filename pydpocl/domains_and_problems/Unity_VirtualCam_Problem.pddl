(define (problem unity-simple-problem)
  (:domain unity-simple-domain)
  (:objects cowboy bandit - person
            duel-right right far-right - place
            master - virtual-shot-cam
			)
  (:init (at bandit far-right)
		 (can-show master far-right)
		 (can-show master duel-right)
		 )
  (:goal (and
            (bel (at bandit duel-right))
		 )
  )
)