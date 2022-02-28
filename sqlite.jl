

using SQLite  # BUT, you use >>DBInterface<< module exported by SQLite!!
using DataFrames


# Create DB and tables. Display tables.
db = SQLite.DB("mydb.sqlite")
SQLite.createtable!(db, "Student", Tables.Schema((:Name, :Grade), (String, Int64)); temp=false, ifnotexists=true)
DBInterface.execute(db, "CREATE TABLE IF NOT EXISTS Student2(Name TEXT, Grade REAL)")
SQLite.columns(db, "Student2")  # sink=columntable
SQLite.tables(db)

# Add vals
DBInterface.execute(db, "INSERT INTO Student VALUES('Peter', 2)")

# Prepared statement: Can use: ?, ?NNN, :AAA, $AAA, @AAA
q = DBInterface.prepare(db, "INSERT INTO Student VALUES(:N, :G)")
DBInterface.execute(q,  Dict(:N=>"George", :G=>"4"))
q = DBInterface.prepare(db, "INSERT INTO Student VALUES(?1, ?2)")
DBInterface.execute(q,  ["George", "4"])

# Query and show
df = DBInterface.execute(db, "SELECT * FROM Student;") |> DataFrames.DataFrame

# Load bulk data in new table
SQLite.load!(df, db, "Student3"; temp=false, ifnotexists=true, replace=false, analyze=false)


# Use this to insert vectors: SQLite.esc_id(q), MAYBE??

# Other stuff that does exist:
SQLite.register(db, func)
SQLite.register(db, init, step_func, final_func; nargs=-1, name=string(step), isdeterm=true)
SQLite.dropindex!(db, index; ifexists::Bool=true)
SQLite.createindex!(db, table, index, cols; unique=true, ifnotexists=false)
SQLite.removeduplicates!(db, table, cols)
SQLite.enable_load_extension(db, enable::Bool=true)
SQLite.indices(db, sink=columntable)
SQLite.drop!(db, table; ifexists::Bool=true)









# JUST USING DBINTERFACE DIRECTLY:

conn = DBInterface.connect(SQLite.DB, "mydb.sqlite")  # (T, args...; kw...) # create a connection to a specific database T; required parameters are database-specific
stmt = DBInterface.prepare(conn, "SELECT * FROM Student;") # prepare a sql statement against the connection; returns a statement object
results = DBInterface.execute(stmt) # execute a prepared statement; returns an iterator of rows (property-accessible & indexable)
results = DBInterface.execute(conn, "SELECT * FROM Student;") # convenience method if statement preparation/re-use isn't needed
rowid = DBInterface.lastrowid(results) # get the last row id of an INSERT statement, as supported by the database
# example of using a query resultset
for row in results
    @show propertynames(row) # see possible column names of row results
    row.col1 # access the value of a column named `col1`
    row[1] # access the first column in the row results
end

# results also implicitly satisfy the Tables.jl `Tables.rows` inteface, so any compatible sink can ingest results
df = DataFrame(results)

# Same as above:
stmt = DBInterface.prepare(conn, "INSERT INTO test_table VALUES(?, ?)") # prepare a statement with positional parameters
DBInterface.execute(stmt, [1, 3.14]) # execute the prepared INSERT statement, passing 1 and 3.14 as positional parameters
stmt = DBInterface.prepare(conn, "INSERT INTO test_table VALUES(:col1, :col2)") # prepare a statement with named parameters
DBInterface.execute(stmt, (col1=1, col2=3.14)) # execute the prepared INSERT statement, with 1 and 3.14 as named parameters

# Nice!!
DBInterface.executemany(stmt, (col1=[1,2,3,4,5], col2=[3.14, 1.23, 2.34 3.45, 4.56])) # execute the prepared statement multiple times for each set of named parameters; each named parameter must be an indexable collection

# Woo
results = DBInterface.executemultiple(conn, sql) # where sql is a query that returns multiple resultsets
# first iterate through resultsets
for result in results
    # for each resultset, we can iterate through resultset rows
    for row in result
        row.col1
    end
end

DBInterface.close!(stmt) # close the prepared statement
DBInterface.close!(conn) # close connection












"""
SELECT c1, c2 FROM t;
SELECT * FROM t;
SELECT c1, c2 FROM t WHERE condition;
SELECT DISTINCT c1 FROM t WHERE condition;
SELECT c1, aggregate(c2) FROM t GROUP BY c1;
SELECT c1, aggregate(c2) FROM t GROUP BY c1 HAVING condition;
SELECT c1, c2 FROM t ORDER BY c1 ASC [DESC];
SELECT c1, c2 FROM t1 UNION [ALL] SELECT c1, c2 FROM t2;
SELECT c1, c2 FROM t1 INTERSECT SELECT c1, c2 FROM t2;
SELECT c1, c2 FROM t1 MINUS SELECT c1, c2 FROM t2;
SELECT c1, c2 FROM t1 WHERE c1 [NOT] LIKE pattern;
SELECT c1, c2 FROM t WHERE c1 [NOT] IN value_list;
SELECT c1, c2 FROM t WHERE c1 BETWEEN low AND high;
SELECT c1, c2 FROM t WHERE c1 IS [NOT] NULL;

SELECT c1, c2 FROM t ORDER BY c1 LIMIT n OFFSET offset;
SELECT c1, c2 FROM t1, t2;
CREATE TABLE t(c1 INT, c2 INT, c3 VARCHAR, PRIMARY KEY (c1,c2));
CREATE TABLE t (id INT PRIMARY KEY, name VARCHAR NOT NULL, price INT DEFAULT 0);
INSERT INTO t(column_list) VALUES(value_list);
INSERT INTO t(column_list) VALUES (value_list), (value_list), ….;
INSERT INTO t1(column_list)
SELECT column_list FROM t2;

UPDATE t SET c1 = new_value, c2 = new_value WHERE condition;
DELETE FROM t;
DELETE FROM t WHERE condition;
DROP TABLE t ;
ALTER TABLE t ADD column;
ALTER TABLE t DROP COLUMN c ;
CREATE TABLE t1(c1 INT PRIMARY KEY, c2 INT, FOREIGN KEY (c2) REFERENCES t2(c2));
CREATE TABLE t(c1 INT, c1 INT, UNIQUE(c2,c3));
CREATE TABLE t(c1 INT, c2 INT, CHECK(c1> 0 AND c1 >= c2));
CREATE TABLE t(c1 INT PRIMARY KEY, c2 VARCHAR NOT NULL);
TRUNCATE TABLE t;
ALTER TABLE t ADD constraint;
ALTER TABLE t DROP constraint;
ALTER TABLE t1 RENAME c1 TO c2 ;
CREATE INDEX idx_name ON t(c1,c2); # t = table name
CREATE VIEW v(c1,c2) AS SELECT c1, c2 FROM t;
CREATE VIEW v(c1,c2) AS SELECT c1, c2 FROM t; WITH [CASCADED | LOCAL] CHECK OPTION;
CREATE RECURSIVE VIEW v AS select-statement -- anchor part UNION [ALL] select-statement; -- recursive part
DROP VIEW view_name
DROP INDEX idx_name;
CREATE OR MODIFY TRIGGER trigger_name WHEN EVENT ON table_name TRIGGER_TYPE
EXECUTE stored_procedure
"""