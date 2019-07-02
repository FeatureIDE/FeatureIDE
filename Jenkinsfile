##Just to test Stuff now please!

pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {
                script {
                    currentBuild.displayName = "The name."
                }    
      			sh '''
               		echo "PATH = ${PATH}"
               		echo "M2_HOME = ${M2_HOME}"
               	'''
            }
        }

        stage ('Test') {
            steps {
                sh 'mvn clean test' 
            }
        }

        stage ('Package') {
        	steps {
        		sh 'mvn clean package'
        	}
        }


        stage ('Verify') {
        	steps {
                sh 'mvn clean verify'
        	}
        }

    }
}
