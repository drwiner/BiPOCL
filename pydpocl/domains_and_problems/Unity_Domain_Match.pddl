(define (domain unity-simple-domain)

    (:types   s-elmnt plan-elmnt cam-param integer - object
		step literal - plan-elmnt
		step-s step-d - step
		step-c - step-d
		operator-type - plan-elmnt
		movable-thing - s-elmnt
		place - s-elmnt
		person thing - movable-thing
		segment - object
		virtual-shot-cam - object
		scale fov angle orient - cam-param
		)
		
	(:constants
		start mid end - segment
		low eye high - angle
		cu full wide - scale
		front behind-right - orient
		0 1 - integer
	)

    (:predicates
		(has ?c - person ?t - thing)
        (at ?thing - movable-thing ?place - place)
        (= ?o1 ?o2 - object)
		(can-show ?cam - virtual-shot-cam ?p - place)
		(obs ?p - plan-elmnt)
		(obs-alu ?p - plan-elmnt)
		(bel ?p - plan-elmn)
		(obs-seg ?s - step-s ?m - segment)
		(obs-seg-alu ?s - step-s ?m - segment)
        )

    (:decomp-predicates
        (arg ?i - integer ?s - plan-elmnt ?o - object)
		(linked-by ?s ?t - step ?l - literal)
		(< ?s1 ?s2 - step)
		(has-scale ?s - step-c ?sc - scale)
		(has-angle ?s - step-c ?a - angle)
		(has-orient ?s - step ?ort - orient)
		(type ?s - step ?t - operator-type)
		(effect ?s - step ?l - literal)
		(precond ?s - step ?l - literal)
		(cntg ?d1 ?d2 - step-d)
		(truth ?l - literal ?j - bool)
	)
                    
    (:action strut
        :type step-s
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (not (= ?p1 ?p2)) )
        :effect(and (not (at ?c ?p1)) (at ?c ?p2))
    )

    (:action cam-shot-start
        :type step-c
        :parameters(?s - step-s ?ort - orient)
        :precondition()
        :effect(obs-seg ?s start)
    )

    (:action cam-shot-end
        :type step-c
        :parameters(?s - step-s ?ort - orient)
        :precondition()
        :effect(obs-seg ?s end)
    )

    (:action basic-match-shot
	    :type step-d
		:parameters(?state - literal)
		:precondition()
		:effect(bel ?state)
		:decomp (
		    :fabula-params (?s - step-s)
	        :fabula-requirements(effect ?s ?state)
			:discourse-params (?c1 ?c2 -  step-c ?o1 ?o2 - orient)
	        :discourse-requirements(and
	            (= ?c1 (cam-shot-start ?s ?o1))
	            (= ?c2 (cam-shot-end ?s ?o2))
                (not (= ?o1 ?o2))
				(cntg ?c1 ?c2)
			)
		)
	)
)