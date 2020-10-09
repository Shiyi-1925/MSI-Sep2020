# KiVa Back-End

KiVa is a powerfull online key-value store. Sort of…
You can use this initial setup to bootstrap any `flask` `anodb` project.


## Practice start

Generate (or possibly copy an existing) SSH public/private key pair protected
by an incredible password:

    sh> ssh-keygen -t rsa -b 2048

And upload the public key (`.ssh/id_rsa.pub`) to your [CRI Gitlab](https://gitlab.cri.mines-paristech.fr/) account.

Configure `git` if needed, eg:

    sh> git config --add user.name "Your Name"
    sh> git config --add user.email "Your Email Address"
    …

In the gitlab interface, fork the
[kiva-zero](https://gitlab.cri.mines-paristech.fr/coelho/kiva-zero/) project as
a private repository, invite group `mobapp` as maintainers, and then clone it locally:

    sh> git clone git@gitlab.cri.mines-paristech.fr:<your-id>/kiva-zero.git kiva-zero


## Back-End Development

This initial working app only implements `/version` which returns a JSON with a few
data, including the time taken from the database. Wow.

Let us develop it further to provide a key-value store available to permitted users.


### Initial Setup

The following files are available in the `back-end` directory:

- [Makefile](Makefile) which wondefully automate some tasks
- [app.py](app.py) a marvellous [Flask](https://flask.palletsprojects.com/) application which gives the time
- [queries.sql](queries.sql) SQL queries for [AnoDB](https://github.com/zx80/anodb)
- [pg.conf](pg.conf) app configuration for [Postgres](https://postgresql.org/)
- [create.sql](create.sql) create application schema
- [drop.sql](drop.sql) drop application schema
- [data.sql](data.sql) insert initial test data
- [truncate.sql](truncate.sql) cleanup schema contents
- [test.py](test.py) [pytest](https://docs.pytest.org/) script

Look at carefully and understand these files.
Do not hesitate to ask questions if in doubt.


### Useful Make Targets

The [Makefile](Makefile) automates some common targets.
Check that you understand how these targets and commands work.

- cleanup generated files, stop everything:

      sh> make clean

- generate the python virtual environment, and use it:

      sh> make venv
      sh> source venv/bin/activate

- start app in dev mode on local port 5000, and check:

      sh> make run
      sh> curl -i http://0.0.0.0:5000/version

- stop running app:

      sh> make stop

- run tests: all, types (mypy), style (flake8) or with a postgres database…

      sh> make check

      sh> make check-types
      sh> make check-style
      sh> make check-pg

Example manual sessions: start the Flask development server, and make HTTP
requests from the command line:

    sh> make run
    # flask app is running against postgres database…

    sh> curl -i -u hobbes:calvin http://0.0.0.0:5000/version
    # GET request, authenticated as `hobbes` with password `calvin`

    sh> curl -i -u calvin:hobbes http://0.0.0.0:5000/store/calvin
    # GET request

    sh> curl -i -X POST -d key=calvin -d val=hobbes -u calvin:hobbes http://0.0.0.0:5000/store
    # POST request with 2 parameters

    sh> curl -i -X DELETE -u hobbes:calvin http://0.0.0.0:5000/store/calvin
    # DELETE request as `hobbes` with password `calvin`

    sh> curl -i -X PATCH -d val=susie http://0.0.0.0:5000/store/calvin
    # PATCH request with 1 parameter

    sh> make stop
    # stop running back-end

File `app.log` contains flask logs. In development, it is also possible to
do some debugging in the browser, although I'm unsure how.


### Development Method

Develop the micro-services described in the next section incrementaly,
using a [TDD - Test-driven development](https://en.wikipedia.org/wiki/Test-driven_development)
approach.

For each addition, proceed as follow:

1. add new success *and* failure tests to
[test.py](test.py), in a *new* test function `test_N`
for each added feature.

2. run new test, checking whether it works or fails as expected.

3. alter kiva schema if needed ([create.sql](create.sql),
[drop.sql](drop.sql),
[data.sql](data.sql) and [truncate.sql](truncate.sql)).

4. add relevant queries to [queries.sql](queries.sql).

5. add or update path handling to [app.py](app.py), ensuring that db
queries are committed on return.

6. run tests, iterating on 3-4-5 till they work.

7. `git commit` and `git push` to [gitlab](https://gitlab.cri.mines-paristech.fr/).

8. refactor code from time to time to improve quality.

Note: the following TDD oriented exercise is somehow too fine grain.
In real life, one test would probably encompass all methods related
to a given path.


### KiVa Micro Services

The provided kiva-zero version implements `GET /version` to return some information.

Develop the following services, in this order, issuing a commit entitled
*Kiva N* where *N* the addition number when the *N*-th feature tests work.

All services must accept HTTP or JSON parameters and return JSON data, if any.
The already predefined `PARAMS` dictionnary allows to manage such parameters
transparently, how nice!

Call must return HTTP success (2XX) or error (4XX) status appropriately.

1. `GET /store` returns the store contents, as a list of tuples.

   For this first feature, you will need to create a new table holding
the key-value pairs.

1. `PUT /store` is not implemented, aka HTTP status 405.

   Just adding a test should be enough.

1. `PATCH /store` is not implemented.

   Idem.

1. `POST /store (key, val)` add a new entry, return HTTP status 201.

   Use the `PARAMS` dictionnary to access parameters.
   Do test both HTTP parameters and JSON.
   Generate a HTTP status 400 if parameters are missing.

1. `DELETE /store` empty store, HTTP status 204.

1. `GET /store (filter)` show store contents whose keys match the `LIKE` filter.

    Modify the existing `GET /store` function to handle an optional `filter` parameter.

1. `DELETE /store (filter)` delete store contents whose keys match the `LIKE` filter.

1. `GET /store/<key>` returns the corresponding value as a simple JSON scalar string,
or HTTP status 404 if the key does not exist.

1. `POST /store/<key>` is not implemented.

1. `PATCH /store/<key> (val)` update associated value.
Return HTTP status 404 if the resource does not exist,
and 400 if the required parameter is missing.

1. `PUT /store/<key> (val)` update associated value.
Return HTTP status 404 if the resource does not exist,
and 400 if the required parameter is missing.
Only write 7 characters to implement this feature.

1. `DELETE /store/<key>` delete value.
Return HTTP status 404 if the resource does not exist.

1. Add a new users concept which will be authorized to perform
some tasks on `/store`: either admin (for `DELETE /store`),
read-only permissions (`GET`) or write (all others) permissions.

   This requires a new table defining users and their associated authorizations,
and then to query this table from each request. Also, authentication needs a
password field which typically holds the salted hash of the user password.
As local tests do not perform an actual authentication, the field value
is not actually used by them. Ensure that authorizations are consistent:
an admin can read and write, write imply read permissions…

   Tests (`test.py`) defines four users: `kiva` who is admin, `calvin` with write,
`hobbes` with read-only and `moe` without access permissions. You initial data (`data.sql`)
*must* define them.  Tests written for previous questions probably assumed admin
rights (the default), so only failure *forbidden* HTTP status code 403 tests need
to be added.

   In `app.py`, define three helper functions `can_read`, `can_write` and `is_admin`
for checking authorizations, that are then called when processing a request:

    ```python
    def get_version():
        if not can_read(LOGIN):
            return Response(status=403)
        …
    ```

1. Using the flask *after request* hook, ensure that all requests end on a `commit`.

1. Using a decorator, improve authorization checks so that the database is not
queried on each request for that purpose by caching positive results…

   ```python
    @CacheOK
    def is_admin(login):
        …
    ```

1. `GET /stats` admin can see `db._count` stats, which is a dictionnary.

1. `GET /users` admin can list users.

1. `GET /users (filter)` admin can list users matching a criteria.

1. `POST /users (login, pw[, is_admin, can_write, can_read])` admin can create a new user,
with default values for the permissions.

1. `PATCH /users/<login> (pw, is_admin, can_write or can_read)` admin can update user data.

1. `PUT /users/<login> (pw, is_admin, can_write or can_read)` admin can update user data.

1. `DELETE /users/<login>` admin can remove a user.

1. All other methods on `/users` and `/users/<login>` are not implemented.

1. Using a decorator, improve authorization checks so that they are declared
on each function rather than explicitely implemented…

   ```python
    @app.route("/version", methods=["GET"]) 
    @RequirePerm(role=READ)
    def get_version():
        …
   ```

1. Review and improve your code…

1. Compare the length of app and test codes. What do you think?
