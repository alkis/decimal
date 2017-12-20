## 2.0.4 (2017-12-04)

- drop -flto because it doesn't seem to work on linux

## 2.0.3 (2017-12-04)

- pass -flto=thin instead of -flto because the latter breaks gcc

## 2.0.2 (2017-12-04)

- replace gcc with cc crate
- pass -flto to the cc compiler if supported

## 2.0.1 (2017-11-30)

- update dependencies

## 2.0 (2017-09-27)

- update dependencies
- status bitflags are moved from `decimal::NAME` to `decimal::Status::NAME`

## 1.0.1 (2017-06-18)

- update dependencies

## 1.0.0 (2016-01-22)

- nothing new added, marking as 1.0.0 as the api has reached maturity

## 0.5.0 (2016-05-18)

- implement the Hash trait (thanks to Mark Edward Sinclair)
- serde support (thanks to Mark Edward Sinclair)

## 0.4.0 (2016-04-15)

- add assignment operators (AddAssign, SubAssign, etc).

## 0.3.1 (2015-01-25)

- add Into<OrdVar<d128>> for more ergonomic use when indexing an OrderedMap with
  a d128

## 0.3.0 (2015-01-24)

- add ord_subset support to enable Eq and Ord for a subset of decimals

## 0.2.0 (2015-12-06)

- works for big and little endian architectures
- add pow, log10, exp, ln

## 0.1.2 (2015-12-13)

- add operator overloads

## 0.1.1 (2015-12-12)

- rustc_serialize support

## 0.1.0 (2015-12-11)

- initial release
