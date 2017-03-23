module sistemaDeIrrigacao

open util/ordering[Time] as to

------------------------------------------------------------- Assinaturas -------------------------------------------------------------

sig Time { }

sig MaquinaDeIrrigacao {
	tanque: one TanqueDeAgua,
	--bateria: one Bateria
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

pred umTanquePorMaquina[m: MaquinaDeIrrigacao] {
	#(m.tanque) = 1
}

/*
pred umaBateriaPorMaquina[m: MaquinaDeIrrigacao] {
	#(m.bateria) = 1
}

pred maximoDeCelulasPorBateria[b: Bateria, t: Time] {
	#(getCelulas[b, t]) <= 3
}

pred bateriaPorMaquina[b:Bateria] {
	one b.~bateria
}
*/

pred tanquePorMaquina[t:TanqueDeAgua] {
	one t.~tanque
}

--pred celulaPorBateria[c:Celula, t:Time] {
	---one c.~(celulas.t)
---}

--pred recarregarBateria[m:MaquinaDeIrrigacao, t: Time] {
--	
--}

------------------------------------------------------------- Funções -------------------------------------------------------------

/*
* Retorna o conjunto de células de uma bateria em um determinado tempo.
*/
fun getCelulas[b:Bateria, t:Time]: set Celula {
	b.(celulas.t)
}

/*
* Retorna a máquina que está ligada ao sensor em um determinado tempo.
*/
fun getMaquina[s:Sensor, t:Time]: one MaquinaDeIrrigacao {
	s.(maquinaNoSensor.t)
}

/*
* Retorna o sensor que está utilizando a máquina em um determinado tempo.
*/
fun getSensor[m: MaquinaDeIrrigacao, t: Time]: one Sensor {
	m.~(maquinaNoSensor.t)
}

------------------------------------------------------------- Fatos -------------------------------------------------------------

fact invariantes {
	
	#MaquinaDeIrrigacao = 4
	--#Bateria = 4
	#TanqueDeAgua = 4
	#Sensor = 5
	#BaseDeEnergia = 0
	#BaseDeAgua = 1

	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]

--	all m:MaquinaDeIrrigacao | umaBateriaPorMaquina[m]

--	all b:Bateria | bateriaPorMaquina[b]

	all t:TanqueDeAgua | tanquePorMaquina[t]

--	all c:Celula, t:Time | celulaPorBateria[c, t]

--	all b: Bateria, t:Time | maximoDeCelulasPorBateria[b, t]

	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, t:Time | (m1 in getMaquina[s1, t] => m2 !in getMaquina[s1, t]) && (s1 in getSensor[m1, t] => s2 !in getSensor[m1, t])

	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, b:BaseDeAgua | m in s.maquinaNoSensor.t => m !in b.maquinaNaBase.t
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, b:BaseDeAgua | m in b.maquinaNaBase.t => m !in s.maquinaNoSensor.t
	
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, b:BaseDeAgua | (m in s.maquinaNoSensor.t and  m !in s.maquinaNoSensor.(t.next)) => m in b.maquinaNaBase.(t.next)
--	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, b:BaseDeAgua | m in b.maquinaNaBase.(t.next) => (m in s.maquinaNoSensor.t and  m !in s.maquinaNoSensor.(t.next))
	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, t:Time, b:BaseDeAgua | m1 in b.maquinaNaBase.t => m2 !in  b.maquinaNaBase.(t.next)
}

pred addMaquinaSensor[m1:MaquinaDeIrrigacao, m2:MaquinaDeIrrigacao - m1, s:Sensor, t,t':Time,  b:BaseDeAgua] {
	m1 !in (s.maquinaNoSensor).t && m2 !in (s.maquinaNoSensor).t
	m1 !in b.maquinaNaBase.t && m2 !in b.maquinaNaBase.t
	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, b:BaseDeAgua, t,t':Time] {
	m in (s.maquinaNoSensor).t 
	m !in b.maquinaNaBase.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m 

	b.maquinaNaBase.t' = b.maquinaNaBase.t + m
--	recarregarBateria[m, t']
}

pred removerDaBase[m:MaquinaDeIrrigacao,  b:BaseDeAgua, t,t':Time] {
	m in b.maquinaNaBase.t
	b.maquinaNaBase.t' = b.maquinaNaBase.t - m
}

pred addMaquinaBaseDeAgua[m1:MaquinaDeIrrigacao, b:Base, s:Sensor, t,t':Time] {
	(m1 !in (b.maquinaNaBase).t) and (m1 in (s.maquinaNoSensor).t)
	(b.maquinaNaBase).t' = (b.maquinaNaBase).t + m1
}

------------------------------------------------------------- Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	no (BaseDeAgua.maquinaNaBase).t
	no (BaseDeAgua.maquinaNaBase).(t.next)
	no (BaseDeEnergia.maquinaNaBase).t
	all b:Bateria | #(getCelulas[b, t]) = 3

}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m1:MaquinaDeIrrigacao, s: Sensor, b:BaseDeAgua | all m2:MaquinaDeIrrigacao |
		addMaquinaSensor[m1, m2, s, pre, pos, b]  or
		removeMaquinaSensor[m1, s, b, pre, pos] or 
		removerDaBase[m1, b, pre, pos]
}

pred show[]  {}

run show for 10


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
