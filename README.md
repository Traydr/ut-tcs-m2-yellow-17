# Software Systems programming project

## Group yellow 17

* Titas Lukaitis
* Beerd van de Streek

### About the repository

This repository contains the two main components of the project:

* The Pentago client
* The Pentago server

These can be found in the packages named `client` and `server` respectively.

### Testing

This project uses JUnit tests. The dependencies used for this are specified in the `pom.xml` file. There are two ways to
run the tests:

#### Testing in the IDE

IntelliJ supports JUnit testing. To run the tests, you can either go to the specific test method or class and click the
green arrow on the left, or you can `right-click` the desired folder and click `Run 'tests in '<folder>''`

#### Run the tests with Maven

In order to run the tests from a command line, you can use Maven. In the project root folder, simply run `mvn verify`.
Maven will search for tests in the project, and run them.

This way of running tests is used in our GitLab pipelines to automatically test the code before merging it. (See `.gitlab-ci.yml`)

### Run instructions

- [ ] TODO

### Build instructions

- [ ] Add Maven option to build client
- [ ] Add Maven option to build server
- [ ] Automatically build in GitLab CI

