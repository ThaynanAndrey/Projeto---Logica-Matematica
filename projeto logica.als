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
	--celulas: Celula -> Time
}

sig Celula {}

sig TanqueDeAgua { }

------------------------------------------------------------- Predicados -------------------------------------------------------------

pred umTanquePorMaquina[m: MaquinaDeIrrigacao] {
	#(m.tanque) = 1
}


pred umaBateriaPorMaquina[m: MaquinaDeIrrigacao] {
	#(m.bateria) = 1
}

/*
pred maximoDeCelulasPorBateria[b: Bateria, t: Time] {
	#(getCelulas[b, t]) <= 3
}
*/

pred bateriaPorMaquina[b:Bateria] {
	one b.~bateria
}


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
--fun getCelulas[b:Bateria, t:Time]: set Celula {
	--b.(celulas.t)
--}

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
	#Bateria = 4
	#TanqueDeAgua = 4
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]

	all m:MaquinaDeIrrigacao | umaBateriaPorMaquina[m]

	all b:Bateria | bateriaPorMaquina[b]

	all t:TanqueDeAgua | tanquePorMaquina[t]

--	all c:Celula, t:Time | celulaPorBateria[c, t]

--	all b: Bateria, t:Time | maximoDeCelulasPorBateria[b, t]

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

--	all m:MaquinaDeIrrigacao, s:Sensor, b:BaseDeAgua | some t:Time | m in b.maquinaNaBase.(t.next) => (m in s.maquinaNoSensor.t and  m !in s.maquinaNoSensor.(t.next))
}

pred addMaquinaSensor[m1:MaquinaDeIrrigacao, s:Sensor, t,t':Time,  bAgua:BaseDeAgua, bEnergia:BaseDeEnergia] {
	m1 !in s.maquinaNoSensor.t
	m1 !in bAgua.maquinaNaBase.t 
	m1 !in bEnergia.maquinaNaBase.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t,t':Time] {
	m in s.maquinaNoSensor.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m
}

pred removerDaBaseAgua[m:MaquinaDeIrrigacao,  bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t,t':Time] {
	m in bAgua.maquinaNaBase.t

	bAgua.maquinaNaBase.t' = bAgua.maquinaNaBase.t - m
}

pred removerDaBaseEnergia[m:MaquinaDeIrrigacao, bEnergia:BaseDeEnergia, t,t':Time] {
	m in bEnergia.maquinaNaBase.t

	bEnergia.maquinaNaBase.t' = bEnergia.maquinaNaBase.t - m
}


pred addMaquinaBaseDeAgua[m:MaquinaDeIrrigacao, bAgua:Base, s:Sensor, t,t':Time] {
	(m !in (bAgua.maquinaNaBase).t) and (m in (s.maquinaNoSensor).t)

	(bAgua.maquinaNaBase).t' = (bAgua.maquinaNaBase).t + m
}

------------------------------------------------------------- Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	no (BaseDeAgua.maquinaNaBase).t
	no (BaseDeAgua.maquinaNaBase).(t.next) // Não precisa
	no (BaseDeEnergia.maquinaNaBase).t
	no (BaseDeEnergia.maquinaNaBase).(t.next) // Não precisa
	no (BaseDeEnergia.maquinaNaBase).(t.next.next) // Não precisa
	--all b:Bateria | #(getCelulas[b, t]) = 3

}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m1:MaquinaDeIrrigacao, s: Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia |
		addMaquinaSensor[m1, s, pre, pos, bAgua, bEnergia]  or
		removeMaquinaSensor[m1, s, bAgua, bEnergia, pre, pos] or
		addMaquinaBaseDeAgua[m1, bAgua, s, pre, pos] or
	    removerDaBaseAgua[m1, bAgua, bEnergia, pre, pos] or
		removerDaBaseEnergia[m1, bEnergia, pre, pos]
}

pred show[]  {}

run show for 8


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
