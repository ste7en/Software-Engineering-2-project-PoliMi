----- SIGNATURES

abstract sig RegisteredEntity {}

sig Individual { }

sig Email { }

sig User extends RegisteredEntity {
	individual: one Individual,
	email: one Email,
	pStatistic: UserReport -> PublicStatistic
}

sig Municipality extends RegisteredEntity {
	referenceCode: one Int,
	dStatistic: UserReport -> DetailedStatistic
} { referenceCode > 0 }

sig Metadata { }

sig Picture {
	width: one Int,
	height: one Int,
	data: one Metadata
} { width > 0 and height > 0}

sig Position {
	latitude: one Int,
	longitude: one Int
} { latitude > 0 and longitude > 0 }

// Fields describing the type of violation and
// the license plate number have been, for simplicity
// reasons, modeled as integers instead of strings
sig UserReport {
	user: one User,
	timestamp: one Int,
	typeOfViolation: one Int,
	licensePlateNumber: one Int,
	picture: one Picture,
	position: one Position
} { licensePlateNumber > 0 and timestamp > 0 and
	(typeOfViolation=0 or typeOfViolation=1 or typeOfViolation=2 or typeOfViolation=3) --for simplicity 4 types of violation
}

one sig SafeStreets {
	registeredUsers: set User,
	registeredMunicipalities: set Municipality,
	pStatistic: UserReport -> PublicStatistic,
	dStatistic: UserReport -> DetailedStatistic
}

abstract sig Filter {
	typeOfViolation: lone Int,
	timestamp: set Int,
	position: set Position
} { (#typeOfViolation>0 or #timestamp>0 or #position>0) }

sig PublicFilter extends Filter {}

sig DetailedFilter extends Filter {
	licensePlateNumber: lone Int,
} { licensePlateNumber > 0}

sig PublicStatistic {
	user: one User,
	pFilter: one PublicFilter
}

sig DetailedStatistic {
	municipality: one Municipality,
	dFilter: one DetailedFilter
}



----- FUNCTIONS

fun getReportsOfDetailedStatistic [ss:SafeStreets, ds: DetailedStatistic]: set UserReport {
	(ss.dStatistic).ds
}

fun getReportsOfPublicStatistic [ss: SafeStreets, ps: PublicStatistic]: set UserReport {
	(ss.pStatistic).ps
}

fun retrieveReportsToDetailedStatistic [ss: SafeStreets, ds: DetailedStatistic]: UserReport -> DetailedStatistic {
	ss.dStatistic :> ds
}

fun retrieveReportsToPublicStatistic [ss:SafeStreets, ps: PublicStatistic]: UserReport -> PublicStatistic {
	ss.pStatistic :> ps
}



----- FACTS

fact uniqueEmailForUsers {
	all e: Email | one u: User | u.email = e
}
fact uniqueRefCodeForMunicipalities {
	all m1, m2: Municipality | (m1 != m2 iff m1.referenceCode != m2.referenceCode)
}
fact allUsersBelongToSafeStreets {
	all u: User | u in SafeStreets.registeredUsers
}
fact allMunicipalitiesBelongToSafeStreets {
	all m: Municipality | m in SafeStreets.registeredMunicipalities
}
fact userIndividualIsUnique {
	all i: Individual | one u: User | u.individual = i
}
fact pictureBelongsToOneReport {
	all p: Picture | one r: UserReport | r.picture = p
}
fact positionBelongsToOneReport {
	all p: Position | one r: UserReport | r.position = p
}
fact metadataBelongsToOnePicture {
	all m: Metadata | one p: Picture | p.data = m
}

fact UserReportBelongsToOneUser {
	all r: UserReport | one u: User | u in r.user
}

fact publicFilterCorrespondsToOnePublicStatistic {
	all pf: PublicFilter | one stat: PublicStatistic | stat.pFilter = pf
}

fact publicStatisticUserIsUnique{
	all ps: PublicStatistic | one u: User | ps.user = u
}

fact detailedStatisticMunicipalityIsUnique{
	all ds: DetailedStatistic | one m: Municipality | ds.municipality = m
}

fact detailedFilterCorrespondsToOneDetailedStatistic {
	all df: DetailedFilter | one stat: DetailedStatistic | stat.dFilter = df
}

fact userReportInMunicipalityImpliesUserReportInSafeStreetsAndViceversa {
	all r: UserReport, ds: DetailedStatistic, ss: SafeStreets, m: Municipality | 	
	r -> ds in m.dStatistic iff r -> ds in ss.dStatistic
}
fact userReportInUserImpliesUserReportInSafeStreetsAndViceversa {
	all r: UserReport, ps: PublicStatistic, ss: SafeStreets, u: User | 	
	r -> ps in u.pStatistic iff r -> ps in ss.pStatistic
}

fact detailedStatisticMadeOfReportsRespectingDetailedFilter {
	all ds: DetailedStatistic, ss: SafeStreets |
	( ( (#(ds.dFilter.timestamp)>0 and ((getReportsOfDetailedStatistic[ss, ds]).timestamp in ds.dFilter.timestamp)) or
		(#(ds.dFilter.timestamp)=0) )
	and
	( (#(ds.dFilter.typeOfViolation)>0 and ((getReportsOfDetailedStatistic[ss, ds]).typeOfViolation = ds.dFilter.typeOfViolation)) or
		(#(ds.dFilter.typeOfViolation)=0) )	
	and
	( (#(ds.dFilter.position)>0 and ((getReportsOfDetailedStatistic[ss, ds]).position in ds.dFilter.position)) or
		(#(ds.dFilter.position)=0) )
	and
	( (#(ds.dFilter.licensePlateNumber)>0 and ((getReportsOfDetailedStatistic[ss, ds]).licensePlateNumber = ds.dFilter.licensePlateNumber)) or
		(#(ds.dFilter.licensePlateNumber)=0) ) )
}

fact publicStatisticMadeOfReportsRespectingPublicFilter {
	all ps: PublicStatistic, ss: SafeStreets |
	( ( (#(ps.pFilter.timestamp)>0 and ((getReportsOfPublicStatistic[ss, ps]).timestamp in ps.pFilter.timestamp)) or
		(#(ps.pFilter.timestamp)=0) )
	and
	( (#(ps.pFilter.typeOfViolation)>0 and ((getReportsOfPublicStatistic[ss, ps]).typeOfViolation = ps.pFilter.typeOfViolation)) or
		(#(ps.pFilter.typeOfViolation)=0) )	
	and
	( (#(ps.pFilter.position)>0 and ((getReportsOfPublicStatistic[ss, ps]).position in ps.pFilter.position)) or
		(#(ps.pFilter.position)=0) ) )
}



----- PREDICATES

pred sendDetailedStatistic[f: DetailedFilter, m: Municipality, m': Municipality, ss: SafeStreets, ds: DetailedStatistic] {
	ds in UserReport.(ss.dStatistic)
	f in ds.dFilter
	m'.referenceCode = m.referenceCode
	m'.dStatistic = m.dStatistic + retrieveReportsToDetailedStatistic[ss, ds]
}

pred sendPublicStatistic[f: PublicFilter, u: User, u': User, ss: SafeStreets, ps: PublicStatistic] {
	ps in UserReport.(ss.pStatistic)
	f in ps.pFilter
	u'.individual = u.individual
	u'.email = u.email
	u'.pStatistic = u.pStatistic + retrieveReportsToPublicStatistic[ss, ps]
}

pred show{}



----- ASSERTIONS

assert sendDetailedStatisticOK {
	all m,m': Municipality, f: DetailedFilter, ss: SafeStreets, ds: DetailedStatistic |
	sendDetailedStatistic[f,m,m',ss,ds] implies
	(
		ds in UserReport.(m'.dStatistic) and
		getReportsOfDetailedStatistic[ss,ds] in m'.dStatistic.DetailedStatistic
	)
}

assert sendPublicStatisticOK {
	all u,u': User, f: PublicFilter, ss: SafeStreets, ps: PublicStatistic |
	sendPublicStatistic[f,u,u',ss,ps] implies
	(
		ps in UserReport.(u'.pStatistic) and
		getReportsOfPublicStatistic[ss,ps] in u'.pStatistic.PublicStatistic
	)
}



----- CHECKS 

check sendDetailedStatisticOK for 10

check sendPublicStatisticOK for 10

----- RUN

run show for 10 but exactly 2 User, exactly 1 Municipality, exactly 4 UserReport, exactly 2 DetailedStatistic, exactly 2 PublicStatistic
