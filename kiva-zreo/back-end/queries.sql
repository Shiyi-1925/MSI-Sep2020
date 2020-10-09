-- SQL queries to be fed to anosdb
-- Use the :param syntax for portability and readability.

-- name: now
SELECT CURRENT_TIMESTAMP;

-- name: getValue
SELECT * FROM kiva; 

-- name: insertValue
INSERT INTO kiva (cle, valeur) VALUES
(:new_cle, :new_valeur);
