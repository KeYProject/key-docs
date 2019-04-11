pipeline {
  agent {
    node {
      label 'master'
    }

  }
  stages {
    stage('Check packages') {
      steps {
        sh 'make prepare'
      }
    }
    stage('Build') {
      steps {
        sh 'make build'
      }
    }
  }
}