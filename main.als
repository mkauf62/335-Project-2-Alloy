abstract sig Vehicle {}
sig PassengerVehicle extends Vehicle {}
sig CargoVehicle extends Vehicle {}

abstract sig Material {
    Quantity: one Int
}
sig Lumber extends Material {}
sig Concrete extends Material {}
sig Steel extends Material {}

sig Materials {
    collection: set Material
}

abstract sig Location {
    job: lone Job,
    vehicles: set Vehicle
}
sig Residence extends Location {}
sig Workplace extends Location {}
sig Warehouse extends Location {}

sig Job{
    Required: Materials
}
fact {
    //All materials must be greater than or equal to 0
    all m: Material | m.Quantity >= 0
}
fact {
  // Jobs must be unique to locations
  all disj x, y : Location | no (x.job & y.job)
}
fact {
  // Jobs must be unique to locations
  all disj x, y : Job | no (x.Required & y.Required)
}
fact {
    // Each vehicle is in one place at a time
    all disj x,y : Location | no (x.vehicles & y.vehicles)
}

run example{}