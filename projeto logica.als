module sistemaDeIrrigacao

open util/ordering[Time] as to

------------------------------------------------------------- Assinaturas -------------------------------------------------------------

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

------------------------------------------------------------- Predicados -------------------------------------------------------------

-- Restringe que cada máquina possui apenas um tanque de água, independente do tempo.
pred umTanquePorMaquina[m: MaquinaDeIrrigacao] {
	one m.tanque
}

-- Restringe que cada tanque pertence à uma única máquina, independente do tempo.
pred umaMaquinaPorTanque[t:TanqueDeAgua] {
	one t.~tanque
}

-- Restringe que cada máquina possui apenas um bateria, independente do tempo.
pred umaBateriaPorMaquina[m: MaquinaDeIrrigacao] {
	one m.bateria
}

-- Restringe que cada bateria pertence à uma única máquina, independente do tempo.
pred umaMaquinaPorBateria[b:Bateria] {
	one b.~bateria
}

-- Restringe que cada bateria possui, no máximo, três células, em um determinado tempo.
pred maximoDeCelulasPorBateria[b: Bateria, t: Time] {
	#(getCelulas[b, t]) <= 3
}

-- Restringe que cada célula pertence à uma única bateria, em um determinado tempo.
pred unicaBateriaPorCelula[c:Celula, t:Time] {
	one c.~(celulas.t)
}

-- Restringe que cada sensor possui uma única máquina, em um determinado tempo.
pred umaMaquinaPorSensor[m1, m2:MaquinaDeIrrigacao, s:Sensor, t:Time] {
	m1 in getMaquina[s, t] => m2 !in getMaquina[s, t]
}

-- Restringe que cada máquina pertence à um único sensor, em um determinado tempo.
pred umSensorPorMaquina[m:MaquinaDeIrrigacao, s1, s2:Sensor, t:Time] {
	s1 in getSensor[m, t] => s2 !in getSensor[m, t]
}

-- Leva uma máquina até o sensor para fazer a irrigação.
pred addMaquinaSensor[m1:MaquinaDeIrrigacao, m2:MaquinaDeIrrigacao - m1, s:Sensor, t,t':Time] {
	m1 !in (s.maquinaNoSensor).t && 	m2 !in (s.maquinaNoSensor).t
	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

-- Faz com que a máquina que estava em um sensor, termine a irrigação e vá reabastecer sua bateria e tanque.
pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, t,t':Time] {
	m in (s.maquinaNoSensor).t
	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m
}

------------------------------------------------------------- Funções -------------------------------------------------------------

-- Retorna o conjunto de células de uma bateria em um determinado tempo.
fun getCelulas[b:Bateria, t:Time]: set Celula {
	b.(celulas.t)
}


-- Retorna a máquina que está ligada ao sensor em um determinado tempo.
fun getMaquina[s:Sensor, t:Time]: one MaquinaDeIrrigacao {
	s.(maquinaNoSensor.t)
}


-- Retorna o sensor que está utilizando a máquina em um determinado tempo.
fun getSensor[m: MaquinaDeIrrigacao, t: Time]: one Sensor {
	m.~(maquinaNoSensor.t)
}

------------------------------------------------------------- Fatos -------------------------------------------------------------

fact invariantes {
	
	#MaquinaDeIrrigacao = 4
	#Bateria = 4
	#TanqueDeAgua = 4
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]

	all t:TanqueDeAgua | umaMaquinaPorTanque[t]

	all m:MaquinaDeIrrigacao | umaBateriaPorMaquina[m]

	all b:Bateria | umaMaquinaPorBateria[b]

	all b: Bateria, t:Time | maximoDeCelulasPorBateria[b, t]

	all c:Celula, t:Time | unicaBateriaPorCelula[c, t]

	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, t:Time | umaMaquinaPorSensor[m1, m2, s1, t] && umSensorPorMaquina[m1, s1, s2, t]

}

------------------------------------------------------------- Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	all b:Bateria | #(getCelulas[b, t]) = 3
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
