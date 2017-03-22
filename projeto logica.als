module sistemaDeIrrigacao

open util/ordering[Time] as to

sig Time { }

sig MaquinaDeIrrigacao {
	tanque: one TanqueDeAgua,
	bateria: one Bateria
}

sig Sensor {
	maquinaNoSensor: MaquinaDeIrrigacao -> Time
}

abstract sig Base { }

sig BaseDeEnergia extends Base { }

sig BaseDeAgua extends Base { }

sig Bateria {
	celulas: Celula -> Time
}

sig Celula { }

sig TanqueDeAgua { }

pred bateriaPorMaquina[b:Bateria] {
	one b.~bateria
}

pred tanquePorMaquina[t:TanqueDeAgua] {
	one t.~tanque
}

pred celulaPorBateria[c:Celula, t:Time] {
	one c.~(celulas.t)
}

fun conjuntoDeCelulas[b:Bateria, t:Time]: set Celula {
	b.(celulas.t)
}

pred addMaquinaSensor[m1:MaquinaDeIrrigacao, m2:MaquinaDeIrrigacao - m1, s:Sensor, t,t':Time] {
	m1 !in (s.maquinaNoSensor).t && 	m2 !in (s.maquinaNoSensor).t
	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

pred removeMaquinaSensor[m1:MaquinaDeIrrigacao, s:Sensor, t,t':Time] {
	m1 in (s.maquinaNoSensor).t
	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m1
}

fact invariantes {
	
	#MaquinaDeIrrigacao = 4
	#Bateria = 4
	#TanqueDeAgua = 4
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

	all m:MaquinaDeIrrigacao | #(m.tanque) = 1

	all m:MaquinaDeIrrigacao | #(m.bateria) = 1

	all b:Bateria | bateriaPorMaquina[b]

	all t:TanqueDeAgua | tanquePorMaquina[t]

	all c:Celula, t:Time | celulaPorBateria[c, t]

	all b:Bateria, t:Time | #(conjuntoDeCelulas[b, t]) = 3

	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, tempo:Time | (m1 in s1.(maquinaNoSensor.tempo)) => m2 !in s1.(maquinaNoSensor.tempo) && (s1 in (m1.~(maquinaNoSensor.tempo)) => s2 !in (m1.~(maquinaNoSensor.tempo))) 

--	all b1:Bateria,b2:Bateria - b1, c1:Celula, c2:Celula - c1, t:Time | (c1 in b1.(celulas.t)) => c2 !in b1.(celulas.t) && (b1 in (c1.~(celulas.t)) => b2 !in (c1.~(celulas.t)))
}

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	#(Bateria.celulas.t) = 12
}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m1:MaquinaDeIrrigacao, s: Sensor | all m2:MaquinaDeIrrigacao |
		addMaquinaSensor[m1, m2, s, pre, pos]  or
		 removeMaquinaSensor[m1, s, pre, pos]
}

pred show[]  {}

run show for 12


-- Adicona tres celulas em uma bateria b
--pred addCelulas[c1, c2, c3:Celula, b:Bateria, t,t':Time] {
--	(c1 !in (b.celulas).t) && (c2 !in (b.celulas).t) && (c3 !in (b.celulas).t)
--	(b.celulas).t' = (b.celulas).t + c1 + c2 + c3
--}

-- Remove uma celula da bateria b
--pred removeCelula[c:Celula, b:Bateria, t,t':Time] {
--	c in (b.celulas).t
--	(b.celulas).t' = (b.celulas).t - c
--}
