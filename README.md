# Software Systems programming project

**Group yellow 17**

* Titas Lukaitis
* Beerd van de Streek

## About the repository

This repository contains the two main components of the project:

* The Pentago client
* The Pentago server

These can be found in the packages named `client` and `server` respectively.

## Testing

This project uses JUnit tests. The dependencies used for this are specified in the `pom.xml` file. There are two ways to
run the tests:

### Testing in the IDE

IntelliJ supports JUnit testing. To run the tests, you can either go to the specific test method or class and click the
green arrow on the left, or you can `right-click` the desired folder and click `Run 'tests in '<folder>''`

### Run the tests with Maven

In order to run the tests from a command line, you can use Maven. In the project root folder, simply run `mvn verify`.
Maven will search for tests in the project, and run them.

This way of running tests is used in our GitLab pipelines to automatically test the code before merging it. (
See `.gitlab-ci.yml`)

## Build instructions

To build the project, you can run `mvn package` in the project root folder. This will put the compiled program in
the `target/` folder.

Optionally, you can also build the project by right-clicking the project root folder in IntelliJ (`yellow-17`) and then
clicking `Build Module 'yellow-17'`

## Run instructions

There are two ways to run the program:

### Run directly in IntelliJ

To run the program directly from IntelliJ, you can go to the desired package (`client` or `server`) and find the main
method. Now click the green arrow to the left of it to run the program in IntelliJ. A `run` window should automatically
pop up after IntelliJ finishes compiling.

### Run from command line

To run the program directly from the command line, you need to manually build the project first. Make sure you followed
the Build instructions above before running.

Now the client can be started by running `java -cp target/<output-file>.jar pentago.client.PentagoClient`
To start the server, run `java -cp target/<output-file>.jar pentago.client.SimplePentagoServer`

**Note:** Make sure to replace `<output-file>` by the actual output file. This should be something
like `yellow17-1.0-SNAPSHOT`

### Download dependencies

To make sure we include the needed dependencies in the repository, we should download them to a local folder. You can do
that by running `mvn dependency:copy-dependencies -DoutputDirectory=$OUTPUT_DIR`. We use `OUTPUT_DIR=./lib` here