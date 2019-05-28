void setBuildStatus(String message, String context, String state) {
  sh '''
    echo "Methode aufgerufen \n"
  '''
}

pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {
                setBuildStatus("Compiling", "compile", "pending");
                sh '''
                    echo "PATH = ${PATH}"
                    echo "M2_HOME = ${M2_HOME}"
                '''
                setBuildStatus("Build complete", "compile", "success");
            }
        }

        stage ('Test') {
            steps {
                setBuildStatus("Compiling", "compile", "pending");
                sh 'mvn clean test' 
                setBuildStatus("Build complete", "compile", "success");
            }
        }

        stage ('Package') {
        	steps {
                setBuildStatus("Compiling", "compile", "pending");
        		sh 'mvn clean package'
                setBuildStatus("Build complete", "compile", "success");
        	}
        }


        stage ('Verify') {
        	steps {
                setBuildStatus("Compiling", "compile", "pending");
        		sh 'mvn clean verify'
                setBuildStatus("Build complete", "compile", "success");
        	}
        }

    }
}