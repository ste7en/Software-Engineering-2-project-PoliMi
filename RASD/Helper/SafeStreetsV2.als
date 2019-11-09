----- SIGNATURES

abstract sig RegisteredEntity {
	--visibilityLevel: one Int
} --{visibilityLevel = 0 or visibilityLevel = 1}

sig Individual { }

sig Email { }

sig User extends RegisteredEntity {
	individual: one Individual,
	email: one Email,
	pStatistic: UserReport -> PublicStatistic
} --{ visibilityLevel = 0 }

sig Municipality extends RegisteredEntity {
	referenceCode: one Int,
	--users: set User,
	dStatistic: UserReport -> DetailedStatistic
} {
	--visibilityLevel = 1 and
	referenceCode > 0
}

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
	timestamp: one Int,
	typeOfViolation: one Int,
	licensePlateNumber: one Int,
	picture: one Picture,
	position: one Position
} { licensePlateNumber > 0 and timestamp > 0 and typeOfViolation > 0 }

one sig SafeStreets {
	registeredUsers: set User,
	registeredMunicipalities: set Municipality,
	violationReports: UserReport -> one User,
	pStatistic: UserReport -> PublicStatistic,
	dStatistic: UserReport -> DetailedStatistic
}

abstract sig Filter {
	typeOfViolation: one Int,
	timestamp: one Int,
	position: one Position
}

sig PublicFilter extends Filter {}

sig DetailedFilter extends Filter {
	email: one Email,
	licensePlateNumber: one Int,
}

sig PublicStatistic {
	pFilter: one PublicFilter
}

sig DetailedStatistic {
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
fact positionBelongsToReport {
	all p: Position | one r: UserReport | r.position = p
}
fact metadataBelongsToOnePicture {
	all m: Metadata | one p: Picture | p.data = m
}
fact allUserReportsBelongToSafeStreets {
	all r: UserReport | one u: User | r -> u in SafeStreets.violationReports
}

fact UserReportInMunicipalityImpliesUserReportInSafeStreets {
	all r: UserReport, ds: DetailedStatistic, ss: SafeStreets, m: Municipality | 	
	r -> ds in m.dStatistic implies r -> ds in ss.dStatistic
}
fact UserReportInUserImpliesUserReportInSafeStreets {
	all r: UserReport, ps: PublicStatistic, ss: SafeStreets, u: User | 	
	r -> ps in u.pStatistic implies r -> ps in ss.pStatistic
}

fact DetailedStatisticMadeOfReportsRespectingDetailedFilter {
	all ds: DetailedStatistic, ss: SafeStreets |
	((getReportsOfDetailedStatistic[ss, ds]).timestamp = ds.dFilter.timestamp) and
	((getReportsOfDetailedStatistic[ss, ds]).typeOfViolation = ds.dFilter.typeOfViolation) and
	((getReportsOfDetailedStatistic[ss, ds]).position = ds.dFilter.position) and
	((getReportsOfDetailedStatistic[ss, ds]).email = ds.dFilter.email) and
	((getReportsOfDetailedStatistic[ss, ds]).licensePlateNumber = ds.dFilter.licensePlateNumber)
}
fact PublicStatisticMadeOfReportsRespectingPublicFilter {
	all ps: PublicStatistic, ss: SafeStreets |
	((getReportsOfPublicStatistic[ss, ps]).timestamp = ps.pFilter.timestamp) and
	((getReportsOfPublicStatistic[ss, ps]).typeOfViolation = ps.pFilter.typeOfViolation) and
	((getReportsOfPublicStatistic[ss, ps]).position = ps.pFilter.position)
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

check sendDetailedStatisticOK for 5

check sendPublicStatisticOK for 5

----- RUN

run show for 5 but exactly 3 User, exactly 4 UserReport, exactly 1 Municipality
