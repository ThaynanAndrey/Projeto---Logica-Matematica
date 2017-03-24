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

abstract sig Base { 
	maquinaNaBase: MaquinaDeIrrigacao -> Time
}

sig BaseDeEnergia extends Base { }

sig BaseDeAgua extends Base { }

sig Bateria {
	celulas: Celula -> Time
}

sig Celula {}

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
pred umaBateriaPorCelula[c:Celula, t:Time] {
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
pred addMaquinaSensor[m1:MaquinaDeIrrigacao, s:Sensor, t,t':Time,  bAgua:BaseDeAgua, bEnergia:BaseDeEnergia] {
	m1 !in s.maquinaNoSensor.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

-- Faz com que a máquina que estava em um sensor, termine a irrigação e vá reabastecer seu tanque e bateria.
pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t,t':Time] {
	m in s.maquinaNoSensor.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m
}

-- Leva uma máquina até a base de água para ter seu tanque reabastecido.
pred addMaquinaBaseDeAgua[m:MaquinaDeIrrigacao, bAgua:BaseDeAgua, s:Sensor, t,t':Time] {
	m !in (bAgua.maquinaNaBase).t
	m in (s.maquinaNoSensor).t

	(bAgua.maquinaNaBase).t' = (bAgua.maquinaNaBase).t + m
}

-- Faz com que a máquina, agora com o tanque cheio, vá reabastecer sua bateria na base de energia.
pred removerDaBaseAgua[m:MaquinaDeIrrigacao,  bAgua:BaseDeAgua, t,t':Time] {
	m in bAgua.maquinaNaBase.t

	bAgua.maquinaNaBase.t' = bAgua.maquinaNaBase.t - m
}

-- Leva uma máquina até a base de energia para ter sua bateria reabastecida, caso necessário.
pred addMaquinaBaseDeEnergia[m:MaquinaDeIrrigacao, bEnergia: BaseDeEnergia, bAgua:BaseDeAgua, t, t':Time] {
	m !in bEnergia.maquinaNaBase.t
	m in bAgua.maquinaNaBase.t

	bEnergia.maquinaNaBase.t' = bEnergia.maquinaNaBase.t + m
}

-- Termina o ciclio da máquina e esta volta ao seu estado inicial.
pred removerDaBaseEnergia[m:MaquinaDeIrrigacao, bEnergia:BaseDeEnergia, t,t':Time] {
	m in bEnergia.maquinaNaBase.t

	bEnergia.maquinaNaBase.t' = bEnergia.maquinaNaBase.t - m
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
	#TanqueDeAgua = 4
	#Bateria = 4
	#Celula = 12
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]

	all t:TanqueDeAgua | umaMaquinaPorTanque[t]

	all m:MaquinaDeIrrigacao | umaBateriaPorMaquina[m]

	all c:Celula, t:Time | umaBateriaPorCelula[c, t]

	all b: Bateria, t:Time | maximoDeCelulasPorBateria[b, t]

-------------------------------------------------------- Sensor --------------------------------------------------------

	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, t:Time | (m1 in getMaquina[s1, t] => m2 !in getMaquina[s1, t]) and (s1 in getSensor[m1, t] => s2 !in getSensor[m1, t])
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | (m in s.maquinaNoSensor.t) => ((m !in bAgua.maquinaNaBase.t) and (m !in bEnergia.maquinaNaBase.t))

-------------------------------------------------------- BaseAgua --------------------------------------------------------

	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | (m in bAgua.maquinaNaBase.t) => ((m !in s.maquinaNoSensor.t) and (m !in bEnergia.maquinaNaBase.t))
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua | (m in s.maquinaNoSensor.t and  m !in s.maquinaNoSensor.(t.next)) => m in bAgua.maquinaNaBase.(t.next)

-------------------------------------------------------- BaseEnergia --------------------------------------------------------

	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | (m in bEnergia.maquinaNaBase.t) => ((m !in s.maquinaNoSensor.t) and (m !in bAgua.maquinaNaBase.t))
	all m:MaquinaDeIrrigacao, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | (m in bAgua.maquinaNaBase.t and m !in bAgua.maquinaNaBase.(t.next)) => m in bEnergia.maquinaNaBase.(t.next)
	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, t:Time, b:Base | m1 in b.maquinaNaBase.t => m2 !in  b.maquinaNaBase.t

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------	

	some m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, t:Time | m in bAgua.maquinaNaBase.t and m in s.maquinaNoSensor.(t.prev)
	some m:MaquinaDeIrrigacao, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t:Time | m in bEnergia.maquinaNaBase.t and m in bAgua.maquinaNaBase.(t.prev)
}

------------------------------------------------------------- Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	no (BaseDeAgua.maquinaNaBase).t
	no (BaseDeAgua.maquinaNaBase).(t.next)
	no (BaseDeEnergia.maquinaNaBase).t
	no (BaseDeEnergia.maquinaNaBase).(t.next)
	no (BaseDeEnergia.maquinaNaBase).(t.next.next)
	all b:Bateria | #(getCelulas[b, t]) = 3
}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m1:MaquinaDeIrrigacao, s: Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia |
		addMaquinaSensor[m1, s, pre, pos, bAgua, bEnergia]  or
		removeMaquinaSensor[m1, s, bAgua, bEnergia, pre, pos] or
		addMaquinaBaseDeAgua[m1, bAgua, s, pre, pos] or
	    removerDaBaseAgua[m1, bAgua, pre, pos] or
		addMaquinaBaseDeEnergia[m1, bEnergia, bAgua, pre, pos] or
		removerDaBaseEnergia[m1, bEnergia, pre, pos]
}

pred show[]  {}

run show for 12
