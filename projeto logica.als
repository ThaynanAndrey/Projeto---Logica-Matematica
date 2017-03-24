module sistemaDeIrrigacao

open util/ordering[Time] as to
open util/boolean

------------------------------------------------------------- Assinaturas -------------------------------------------------------------

sig Time { }

sig MaquinaDeIrrigacao {
	tanque: one TanqueDeAgua
}

sig TanqueDeAgua {
	cheio: Bool -> Time
}

sig Sensor {
	maquinaNoSensor: MaquinaDeIrrigacao -> Time
}

abstract sig Base { 
	maquinaNaBase: MaquinaDeIrrigacao -> Time
}

sig BaseDeAgua extends Base { }

------------------------------------------------------------- Predicados -------------------------------------------------------------

pred umTanquePorMaquina[m: MaquinaDeIrrigacao] {
	one m.tanque
}

pred tanqueApenasEmUmaMaquina[tanqueDeAgua:TanqueDeAgua] {
	one tanqueDeAgua.~tanque
}

pred ouCheioOuVazio[tanqueDeAgua:TanqueDeAgua, t:Time] {
	one tanqueDeAgua.cheio.t
}

------------------------------------------------------------- Funções -------------------------------------------------------------

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

fun tanqueEstaCheio[tanqueDeAgua:TanqueDeAgua, t:Time]: one Bool {
	tanqueDeAgua.cheio.t
}

------------------------------------------------------------- Fatos -------------------------------------------------------------

fact quantidades {
	#MaquinaDeIrrigacao = 4
	#TanqueDeAgua = 4
	#Sensor = 5
	#BaseDeAgua = 1
}

fact invariantes {
	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]
	all tanqueDeAgua:TanqueDeAgua | tanqueApenasEmUmaMaquina[tanqueDeAgua]
	all tanqueDeAgua:TanqueDeAgua, t:Time | ouCheioOuVazio[tanqueDeAgua, t]

	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, t:Time | (m1 in getMaquina[s1, t] => m2 !in getMaquina[s1, t]) and (s1 in getSensor[m1, t] => s2 !in getSensor[m1, t])
	all m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, t:Time | (m in s.maquinaNoSensor.t) => (m !in bAgua.maquinaNaBase.t)
	all m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, t:Time | (m in bAgua.maquinaNaBase.t) => (m !in s.maquinaNoSensor.t)
}

fact Sequenciais {
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time | (m in s.maquinaNoSensor.t and m !in s.maquinaNoSensor.(t.next)) => !(isTrue[(m.tanque.cheio.(t.next))])
	all m:MaquinaDeIrrigacao, bAgua:BaseDeAgua, t:Time | (m in bAgua.maquinaNaBase.t and m !in bAgua.maquinaNaBase.(t.next)) => (isTrue[(m.tanque.cheio.(t.next))])
	all m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua | some t:Time | (m in s.maquinaNoSensor.t and m !in s.maquinaNoSensor.(t.next)) => (m in bAgua.maquinaNaBase.(t.next))
	all m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, t:Time | (m !in s.maquinaNoSensor.t) => (m !in bAgua.maquinaNaBase.(t.next))
}

------------------------------------------------------------- Ações -------------------------------------------------------------

pred addMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor,  bAgua:BaseDeAgua, t,t':Time] {
	m !in s.maquinaNoSensor.t
	m !in bAgua.maquinaNaBase.t
	isTrue[m.tanque.cheio.t]

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m
}

pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, t,t':Time] {
	m in s.maquinaNoSensor.t
	!isTrue[m.tanque.cheio.t']

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m
}

pred addMaquinaBaseDeAgua[m:MaquinaDeIrrigacao, bAgua:Base, s:Sensor, t,t':Time] {
	m !in (bAgua.maquinaNaBase).t
	m in (s.maquinaNoSensor).t
	!isTrue[m.tanque.cheio.t]

	(bAgua.maquinaNaBase).t' = (bAgua.maquinaNaBase).t + m
}

pred removerDaBaseAgua[m:MaquinaDeIrrigacao,  bAgua:BaseDeAgua, t,t':Time] {
	m in bAgua.maquinaNaBase.t
	isTrue[m.tanque.cheio.t']

	bAgua.maquinaNaBase.t' = bAgua.maquinaNaBase.t - m
}

pred encheTanque[tanqueDeAgua:TanqueDeAgua, t, t':Time] {
	!isTrue[tanqueDeAgua.cheio.t]

	tanqueDeAgua.cheio.t' = True
}

pred esvaziaTanque[tanqueDeAgua:TanqueDeAgua, t, t':Time] {
	isTrue[tanqueDeAgua.cheio.t]

	tanqueDeAgua.cheio.t' = False
}

------------------------------------------------------------- Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	no (BaseDeAgua.maquinaNaBase).t
	no (BaseDeAgua.maquinaNaBase).t.next // Are you smelling that smelly smell?
	all tanqueDeAgua:TanqueDeAgua | tanqueDeAgua.cheio.t = True
}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m:MaquinaDeIrrigacao, tanqueDeAgua:TanqueDeAgua, s: Sensor, bAgua:BaseDeAgua |
		addMaquinaSensor[m, s, bAgua, pre, pos]  or
		removeMaquinaSensor[m, s, bAgua, pre, pos] or
		addMaquinaBaseDeAgua[m, bAgua, s, pre, pos] or
		removerDaBaseAgua[m, bAgua, pre, pos] or
		encheTanque[tanqueDeAgua, pre, pos] or
		esvaziaTanque[tanqueDeAgua, pre, pos]
}

pred show[]  {}

run show for 6
